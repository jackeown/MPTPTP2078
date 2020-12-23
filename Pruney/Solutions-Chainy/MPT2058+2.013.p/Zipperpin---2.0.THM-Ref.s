%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EedVwnyPGo

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  260 ( 935 expanded)
%              Number of leaves         :   42 ( 306 expanded)
%              Depth                    :   36
%              Number of atoms          : 3261 (16142 expanded)
%              Number of equality atoms :   43 ( 220 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(r1_waybel_7_type,type,(
    r1_waybel_7: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t17_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r3_waybel_9 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C )
              <=> ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
              & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r3_waybel_9 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C )
                <=> ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_yellow19])).

thf('0',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('12',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(fc5_yellow19,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ~ ( v1_xboole_0 @ C )
        & ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) )
        & ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A )
        & ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_xboole_0 @ X17 )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ ( u1_struct_0 @ ( k3_yellow_1 @ X17 ) ) )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_yellow_1 @ X17 ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_yellow_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X17 ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X18 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow19])).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('23',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('24',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_xboole_0 @ X17 )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) )
      | ~ ( v2_waybel_0 @ X19 @ ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) )
      | ~ ( v13_waybel_0 @ X19 @ ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X17 ) ) ) ) )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X18 @ X17 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('31',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('40',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('49',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['26','35','44','53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','54'])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(fc4_yellow19,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ~ ( v1_xboole_0 @ C )
        & ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ) )).

thf('62',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_yellow_1 @ X14 ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_yellow_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X14 ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X15 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_yellow19])).

thf('63',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('64',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('65',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('66',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v2_waybel_0 @ X16 @ ( k3_lattice3 @ ( k1_lattice3 @ X14 ) ) )
      | ~ ( v13_waybel_0 @ X16 @ ( k3_lattice3 @ ( k1_lattice3 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X14 ) ) ) ) )
      | ( v4_orders_2 @ ( k3_yellow19 @ X15 @ X14 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('69',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','70'])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('76',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(dt_k3_yellow19,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ~ ( v1_xboole_0 @ C )
        & ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) )
        & ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A )
        & ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ) )).

thf('78',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v2_waybel_0 @ X13 @ ( k3_yellow_1 @ X11 ) )
      | ~ ( v13_waybel_0 @ X13 @ ( k3_yellow_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X11 ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X12 @ X11 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('79',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('80',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('81',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('82',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v2_waybel_0 @ X13 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) )
      | ~ ( v13_waybel_0 @ X13 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ) )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X12 @ X11 @ X13 ) @ X12 ) ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('85',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['76','86'])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('92',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('95',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['92','94'])).

thf('96',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['91','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r3_waybel_9 @ A @ B @ C )
              <=> ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) )).

thf('100',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r3_waybel_9 @ X21 @ X20 @ X22 )
      | ( r1_waybel_7 @ X21 @ ( k2_yellow19 @ X21 @ X20 ) @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C_1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C_1 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ X0 ) @ sk_C_1 )
      | ~ ( r3_waybel_9 @ sk_A @ X0 @ sk_C_1 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['98','104'])).

thf('106',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C_1 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['90','105'])).

thf('107',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C_1 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['74','107'])).

thf('109',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','109'])).

thf('111',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('112',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('113',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('114',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t15_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( B
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('115',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_subset_1 @ X23 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X24 ) ) ) )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_yellow_1 @ ( k2_struct_0 @ X24 ) ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_yellow_1 @ ( k2_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X24 ) ) ) ) )
      | ( X23
        = ( k2_yellow19 @ X24 @ ( k3_yellow19 @ X24 @ ( k2_struct_0 @ X24 ) @ X23 ) ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t15_yellow19])).

thf('116',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('117',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('118',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('119',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('120',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_subset_1 @ X23 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X24 ) ) ) ) )
      | ~ ( v2_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X24 ) ) ) )
      | ~ ( v13_waybel_0 @ X23 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X24 ) ) ) ) ) )
      | ( X23
        = ( k2_yellow19 @ X24 @ ( k3_yellow19 @ X24 @ ( k2_struct_0 @ X24 ) @ X23 ) ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['114','120'])).

thf('122',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('123',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('124',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['113','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['112','132'])).

thf('134',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['111','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['110','136'])).

thf('138',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('140',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('141',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v2_waybel_0 @ X13 @ ( k3_yellow_1 @ X11 ) )
      | ~ ( v13_waybel_0 @ X13 @ ( k3_yellow_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X11 ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow19])).

thf('142',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('143',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('144',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('145',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v2_waybel_0 @ X13 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) )
      | ~ ( v13_waybel_0 @ X13 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X11 ) ) ) ) )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X12 @ X11 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['140','145'])).

thf('147',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('148',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','149'])).

thf('151',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['138','150'])).

thf('152',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','152'])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
   <= ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('157',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('162',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('163',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','165'])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('170',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('171',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('172',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('173',plain,
    ( ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('174',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('175',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('176',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('177',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('178',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r1_waybel_7 @ X21 @ ( k2_yellow19 @ X21 @ X20 ) @ X22 )
      | ( r3_waybel_9 @ X21 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow19])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['176','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['173','188'])).

thf('190',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) )
   <= ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('193',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('194',plain,
    ( ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['191','194'])).

thf('196',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['172','195'])).

thf('197',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','149'])).

thf('200',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['171','201'])).

thf('203',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['204','205'])).

thf('207',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('210',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['210','211'])).

thf('213',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 )
      & ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['170','212'])).

thf('214',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ~ ( r1_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
    | ( r3_waybel_9 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','168','169','215'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EedVwnyPGo
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 194 iterations in 0.099s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.21/0.56  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.56  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.56  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 0.21/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.56  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.21/0.56  thf(r1_waybel_7_type, type, r1_waybel_7: $i > $i > $i > $o).
% 0.21/0.56  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.56  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.56  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.21/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.56  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.56  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.21/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(t17_yellow19, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.56             ( v1_subset_1 @
% 0.21/0.56               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.56             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.56             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.56             ( m1_subset_1 @
% 0.21/0.56               B @ 
% 0.21/0.56               ( k1_zfmisc_1 @
% 0.21/0.56                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56               ( ( r3_waybel_9 @
% 0.21/0.56                   A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.21/0.56                 ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.56            ( l1_pre_topc @ A ) ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.56                ( v1_subset_1 @
% 0.21/0.56                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.21/0.56                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.56                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.21/0.56                ( m1_subset_1 @
% 0.21/0.56                  B @ 
% 0.21/0.56                  ( k1_zfmisc_1 @
% 0.21/0.56                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.21/0.56              ( ![C:$i]:
% 0.21/0.56                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56                  ( ( r3_waybel_9 @
% 0.21/0.56                      A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) @ C ) <=>
% 0.21/0.56                    ( r1_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t17_yellow19])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.21/0.56        | ~ (r3_waybel_9 @ sk_A @ 
% 0.21/0.56             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.21/0.56       ~
% 0.21/0.56       ((r3_waybel_9 @ sk_A @ 
% 0.21/0.56         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf(dt_l1_pre_topc, axiom,
% 0.21/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.56  thf('2', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.56  thf('3', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.56  thf('4', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.56  thf(d3_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.56  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.56  thf(t3_subset, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X4 : $i, X6 : $i]:
% 0.21/0.56         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.56  thf('10', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf('11', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.56  thf(d3_struct_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X7 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ 
% 0.21/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d2_yellow_1, axiom,
% 0.21/0.56    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.21/0.56      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (((m1_subset_1 @ sk_B @ 
% 0.21/0.56         (k1_zfmisc_1 @ 
% 0.21/0.56          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['12', '15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | (m1_subset_1 @ sk_B @ 
% 0.21/0.56           (k1_zfmisc_1 @ 
% 0.21/0.56            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['11', '16'])).
% 0.21/0.56  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.21/0.56      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.56  thf(fc5_yellow19, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.56         ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.56         ( ~( v1_xboole_0 @ C ) ) & 
% 0.21/0.56         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.21/0.56         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.56         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.56         ( m1_subset_1 @
% 0.21/0.56           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.21/0.56       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.21/0.56         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.21/0.56         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.56          | (v1_xboole_0 @ X17)
% 0.21/0.56          | ~ (l1_struct_0 @ X18)
% 0.21/0.56          | (v2_struct_0 @ X18)
% 0.21/0.56          | (v1_xboole_0 @ X19)
% 0.21/0.56          | ~ (v1_subset_1 @ X19 @ (u1_struct_0 @ (k3_yellow_1 @ X17)))
% 0.21/0.56          | ~ (v2_waybel_0 @ X19 @ (k3_yellow_1 @ X17))
% 0.21/0.56          | ~ (v13_waybel_0 @ X19 @ (k3_yellow_1 @ X17))
% 0.21/0.56          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X17))))
% 0.21/0.56          | (v7_waybel_0 @ (k3_yellow19 @ X18 @ X17 @ X19)))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.56          | (v1_xboole_0 @ X17)
% 0.21/0.56          | ~ (l1_struct_0 @ X18)
% 0.21/0.56          | (v2_struct_0 @ X18)
% 0.21/0.56          | (v1_xboole_0 @ X19)
% 0.21/0.56          | ~ (v1_subset_1 @ X19 @ 
% 0.21/0.56               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X17))))
% 0.21/0.56          | ~ (v2_waybel_0 @ X19 @ (k3_lattice3 @ (k1_lattice3 @ X17)))
% 0.21/0.56          | ~ (v13_waybel_0 @ X19 @ (k3_lattice3 @ (k1_lattice3 @ X17)))
% 0.21/0.56          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X17)))))
% 0.21/0.56          | (v7_waybel_0 @ (k3_yellow19 @ X18 @ X17 @ X19)))),
% 0.21/0.56      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.56          | ~ (v13_waybel_0 @ sk_B @ 
% 0.21/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.56          | ~ (v2_waybel_0 @ sk_B @ 
% 0.21/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.56          | ~ (v1_subset_1 @ sk_B @ 
% 0.21/0.56               (u1_struct_0 @ 
% 0.21/0.56                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.56          | (v1_xboole_0 @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (l1_struct_0 @ X0)
% 0.21/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['19', '25'])).
% 0.21/0.56  thf('27', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X7 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (((v13_waybel_0 @ sk_B @ 
% 0.21/0.56         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['28', '31'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | (v13_waybel_0 @ sk_B @ 
% 0.21/0.56           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['27', '32'])).
% 0.21/0.56  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('36', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X7 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (((v2_waybel_0 @ sk_B @ 
% 0.21/0.56         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['37', '40'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | (v2_waybel_0 @ sk_B @ 
% 0.21/0.56           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['36', '41'])).
% 0.21/0.56  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.56  thf('45', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      (![X7 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      ((v1_subset_1 @ sk_B @ 
% 0.21/0.56        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      ((v1_subset_1 @ sk_B @ 
% 0.21/0.56        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (((v1_subset_1 @ sk_B @ 
% 0.21/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['46', '49'])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | (v1_subset_1 @ sk_B @ 
% 0.21/0.56           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['45', '50'])).
% 0.21/0.56  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      ((v1_subset_1 @ sk_B @ 
% 0.21/0.56        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.56          | (v1_xboole_0 @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (l1_struct_0 @ X0)
% 0.21/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['26', '35', '44', '53'])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.56        | (v2_struct_0 @ sk_A)
% 0.21/0.56        | (v1_xboole_0 @ sk_B)
% 0.21/0.56        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['10', '54'])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.56        | (v1_xboole_0 @ sk_B)
% 0.21/0.56        | (v2_struct_0 @ sk_A)
% 0.21/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '55'])).
% 0.21/0.56  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.56        | (v1_xboole_0 @ sk_B)
% 0.21/0.56        | (v2_struct_0 @ sk_A)
% 0.21/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.56  thf('59', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.56  thf('60', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.21/0.56      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.56  thf(fc4_yellow19, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.56         ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.56         ( ~( v1_xboole_0 @ C ) ) & 
% 0.21/0.56         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.56         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.56         ( m1_subset_1 @
% 0.21/0.56           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.21/0.56       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.21/0.56         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.21/0.56         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.21/0.56         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.56          | (v1_xboole_0 @ X14)
% 0.21/0.56          | ~ (l1_struct_0 @ X15)
% 0.21/0.56          | (v2_struct_0 @ X15)
% 0.21/0.56          | (v1_xboole_0 @ X16)
% 0.21/0.56          | ~ (v2_waybel_0 @ X16 @ (k3_yellow_1 @ X14))
% 0.21/0.56          | ~ (v13_waybel_0 @ X16 @ (k3_yellow_1 @ X14))
% 0.21/0.56          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X14))))
% 0.21/0.56          | (v4_orders_2 @ (k3_yellow19 @ X15 @ X14 @ X16)))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.21/0.56  thf('63', plain,
% 0.21/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('64', plain,
% 0.21/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('66', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.56          | (v1_xboole_0 @ X14)
% 0.21/0.56          | ~ (l1_struct_0 @ X15)
% 0.21/0.56          | (v2_struct_0 @ X15)
% 0.21/0.56          | (v1_xboole_0 @ X16)
% 0.21/0.56          | ~ (v2_waybel_0 @ X16 @ (k3_lattice3 @ (k1_lattice3 @ X14)))
% 0.21/0.56          | ~ (v13_waybel_0 @ X16 @ (k3_lattice3 @ (k1_lattice3 @ X14)))
% 0.21/0.56          | ~ (m1_subset_1 @ X16 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X14)))))
% 0.21/0.56          | (v4_orders_2 @ (k3_yellow19 @ X15 @ X14 @ X16)))),
% 0.21/0.56      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.56          | ~ (v13_waybel_0 @ sk_B @ 
% 0.21/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.56          | ~ (v2_waybel_0 @ sk_B @ 
% 0.21/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.56          | (v1_xboole_0 @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (l1_struct_0 @ X0)
% 0.21/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['61', '66'])).
% 0.21/0.56  thf('68', plain,
% 0.21/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('69', plain,
% 0.21/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.56  thf('70', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.56          | (v1_xboole_0 @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (l1_struct_0 @ X0)
% 0.21/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.56  thf('71', plain,
% 0.21/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.56        | (v2_struct_0 @ sk_A)
% 0.21/0.56        | (v1_xboole_0 @ sk_B)
% 0.21/0.56        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['60', '70'])).
% 0.21/0.56  thf('72', plain,
% 0.21/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.56        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.56        | (v1_xboole_0 @ sk_B)
% 0.21/0.56        | (v2_struct_0 @ sk_A)
% 0.21/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['59', '71'])).
% 0.21/0.56  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('74', plain,
% 0.21/0.56      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.56        | (v1_xboole_0 @ sk_B)
% 0.21/0.56        | (v2_struct_0 @ sk_A)
% 0.21/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['72', '73'])).
% 0.21/0.56  thf('75', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.56  thf('76', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf('77', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_B @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.21/0.56      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.56  thf(dt_k3_yellow19, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.56         ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.56         ( ~( v1_xboole_0 @ C ) ) & 
% 0.21/0.56         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.56         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.21/0.56         ( m1_subset_1 @
% 0.21/0.56           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.21/0.56       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.21/0.56         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.21/0.56         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.21/0.56  thf('78', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.56          | (v1_xboole_0 @ X11)
% 0.21/0.56          | ~ (l1_struct_0 @ X12)
% 0.21/0.56          | (v2_struct_0 @ X12)
% 0.21/0.56          | (v1_xboole_0 @ X13)
% 0.21/0.56          | ~ (v2_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.21/0.56          | ~ (v13_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.21/0.56          | ~ (m1_subset_1 @ X13 @ 
% 0.21/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X11))))
% 0.21/0.56          | (l1_waybel_0 @ (k3_yellow19 @ X12 @ X11 @ X13) @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.21/0.56  thf('79', plain,
% 0.21/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('80', plain,
% 0.21/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('81', plain,
% 0.21/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.21/0.56  thf('82', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.56          | (v1_xboole_0 @ X11)
% 0.21/0.56          | ~ (l1_struct_0 @ X12)
% 0.21/0.56          | (v2_struct_0 @ X12)
% 0.21/0.56          | (v1_xboole_0 @ X13)
% 0.21/0.56          | ~ (v2_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.21/0.56          | ~ (v13_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.21/0.56          | ~ (m1_subset_1 @ X13 @ 
% 0.21/0.56               (k1_zfmisc_1 @ 
% 0.21/0.56                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X11)))))
% 0.21/0.56          | (l1_waybel_0 @ (k3_yellow19 @ X12 @ X11 @ X13) @ X12))),
% 0.21/0.56      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.21/0.56  thf('83', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.56          | ~ (v13_waybel_0 @ sk_B @ 
% 0.21/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.56          | ~ (v2_waybel_0 @ sk_B @ 
% 0.21/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.21/0.56          | (v1_xboole_0 @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (l1_struct_0 @ X0)
% 0.21/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['77', '82'])).
% 0.21/0.56  thf('84', plain,
% 0.21/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.21/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('85', plain,
% 0.21/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.21/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.56  thf('86', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.21/0.56          | (v1_xboole_0 @ sk_B)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (l1_struct_0 @ X0)
% 0.21/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.39/0.56  thf('87', plain,
% 0.39/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | (v1_xboole_0 @ sk_B)
% 0.39/0.56        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.39/0.56           sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['76', '86'])).
% 0.39/0.56  thf('88', plain,
% 0.39/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.56        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.39/0.56           sk_A)
% 0.39/0.56        | (v1_xboole_0 @ sk_B)
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['75', '87'])).
% 0.39/0.56  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('90', plain,
% 0.39/0.56      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.39/0.56         sk_A)
% 0.39/0.56        | (v1_xboole_0 @ sk_B)
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['88', '89'])).
% 0.39/0.56  thf('91', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.56  thf('92', plain,
% 0.39/0.56      (![X7 : $i]:
% 0.39/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.56  thf('93', plain,
% 0.39/0.56      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.39/0.56        | (r3_waybel_9 @ sk_A @ 
% 0.39/0.56           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('94', plain,
% 0.39/0.56      (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('split', [status(esa)], ['93'])).
% 0.39/0.56  thf('95', plain,
% 0.39/0.56      ((((r3_waybel_9 @ sk_A @ 
% 0.39/0.56          (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C_1)
% 0.39/0.56         | ~ (l1_struct_0 @ sk_A)))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('sup+', [status(thm)], ['92', '94'])).
% 0.39/0.56  thf('96', plain,
% 0.39/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.39/0.56         | (r3_waybel_9 @ sk_A @ 
% 0.39/0.56            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['91', '95'])).
% 0.39/0.56  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('98', plain,
% 0.39/0.56      (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56         (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C_1))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['96', '97'])).
% 0.39/0.56  thf('99', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t12_yellow19, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.39/0.56             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.39/0.56           ( ![C:$i]:
% 0.39/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.56               ( ( r3_waybel_9 @ A @ B @ C ) <=>
% 0.39/0.56                 ( r1_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.39/0.56  thf('100', plain,
% 0.39/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.56         ((v2_struct_0 @ X20)
% 0.39/0.56          | ~ (v4_orders_2 @ X20)
% 0.39/0.56          | ~ (v7_waybel_0 @ X20)
% 0.39/0.56          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.39/0.56          | ~ (r3_waybel_9 @ X21 @ X20 @ X22)
% 0.39/0.56          | (r1_waybel_7 @ X21 @ (k2_yellow19 @ X21 @ X20) @ X22)
% 0.39/0.56          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.39/0.56          | ~ (l1_pre_topc @ X21)
% 0.39/0.56          | ~ (v2_pre_topc @ X21)
% 0.39/0.56          | (v2_struct_0 @ X21))),
% 0.39/0.56      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.39/0.56  thf('101', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((v2_struct_0 @ sk_A)
% 0.39/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.56          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C_1)
% 0.39/0.56          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C_1)
% 0.39/0.56          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.39/0.56          | ~ (v7_waybel_0 @ X0)
% 0.39/0.56          | ~ (v4_orders_2 @ X0)
% 0.39/0.56          | (v2_struct_0 @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['99', '100'])).
% 0.39/0.56  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('104', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((v2_struct_0 @ sk_A)
% 0.39/0.56          | (r1_waybel_7 @ sk_A @ (k2_yellow19 @ sk_A @ X0) @ sk_C_1)
% 0.39/0.56          | ~ (r3_waybel_9 @ sk_A @ X0 @ sk_C_1)
% 0.39/0.56          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.39/0.56          | ~ (v7_waybel_0 @ X0)
% 0.39/0.56          | ~ (v4_orders_2 @ X0)
% 0.39/0.56          | (v2_struct_0 @ X0))),
% 0.39/0.56      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.39/0.56  thf('105', plain,
% 0.39/0.56      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | ~ (l1_waybel_0 @ 
% 0.39/0.56              (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.39/0.56         | (r1_waybel_7 @ sk_A @ 
% 0.39/0.56            (k2_yellow19 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.39/0.56            sk_C_1)
% 0.39/0.56         | (v2_struct_0 @ sk_A)))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['98', '104'])).
% 0.39/0.56  thf('106', plain,
% 0.39/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (r1_waybel_7 @ sk_A @ 
% 0.39/0.56            (k2_yellow19 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.39/0.56            sk_C_1)
% 0.39/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['90', '105'])).
% 0.39/0.56  thf('107', plain,
% 0.39/0.56      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | (r1_waybel_7 @ sk_A @ 
% 0.39/0.56            (k2_yellow19 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.39/0.56            sk_C_1)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['106'])).
% 0.39/0.56  thf('108', plain,
% 0.39/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (r1_waybel_7 @ sk_A @ 
% 0.39/0.56            (k2_yellow19 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.39/0.56            sk_C_1)
% 0.39/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['74', '107'])).
% 0.39/0.56  thf('109', plain,
% 0.39/0.56      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | (r1_waybel_7 @ sk_A @ 
% 0.39/0.56            (k2_yellow19 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.39/0.56            sk_C_1)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['108'])).
% 0.39/0.56  thf('110', plain,
% 0.39/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (r1_waybel_7 @ sk_A @ 
% 0.39/0.56            (k2_yellow19 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.39/0.56            sk_C_1)
% 0.39/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['58', '109'])).
% 0.39/0.56  thf('111', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.56  thf('112', plain,
% 0.39/0.56      (![X7 : $i]:
% 0.39/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.56  thf('113', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.56  thf('114', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_B @ 
% 0.39/0.56        (k1_zfmisc_1 @ 
% 0.39/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.39/0.56      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.56  thf(t15_yellow19, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.39/0.56             ( v1_subset_1 @
% 0.39/0.56               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.39/0.56             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.39/0.56             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.39/0.56             ( m1_subset_1 @
% 0.39/0.56               B @ 
% 0.39/0.56               ( k1_zfmisc_1 @
% 0.39/0.56                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.39/0.56           ( ( B ) =
% 0.39/0.56             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.39/0.56  thf('115', plain,
% 0.39/0.56      (![X23 : $i, X24 : $i]:
% 0.39/0.56         ((v1_xboole_0 @ X23)
% 0.39/0.56          | ~ (v1_subset_1 @ X23 @ 
% 0.39/0.56               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X24))))
% 0.39/0.56          | ~ (v2_waybel_0 @ X23 @ (k3_yellow_1 @ (k2_struct_0 @ X24)))
% 0.39/0.56          | ~ (v13_waybel_0 @ X23 @ (k3_yellow_1 @ (k2_struct_0 @ X24)))
% 0.39/0.56          | ~ (m1_subset_1 @ X23 @ 
% 0.39/0.56               (k1_zfmisc_1 @ 
% 0.39/0.56                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X24)))))
% 0.39/0.56          | ((X23)
% 0.39/0.56              = (k2_yellow19 @ X24 @ 
% 0.39/0.56                 (k3_yellow19 @ X24 @ (k2_struct_0 @ X24) @ X23)))
% 0.39/0.56          | ~ (l1_struct_0 @ X24)
% 0.39/0.56          | (v2_struct_0 @ X24))),
% 0.39/0.56      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.39/0.56  thf('116', plain,
% 0.39/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.56  thf('117', plain,
% 0.39/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.56  thf('118', plain,
% 0.39/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.56  thf('119', plain,
% 0.39/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.56  thf('120', plain,
% 0.39/0.56      (![X23 : $i, X24 : $i]:
% 0.39/0.56         ((v1_xboole_0 @ X23)
% 0.39/0.56          | ~ (v1_subset_1 @ X23 @ 
% 0.39/0.56               (u1_struct_0 @ 
% 0.39/0.56                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24)))))
% 0.39/0.56          | ~ (v2_waybel_0 @ X23 @ 
% 0.39/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24))))
% 0.39/0.56          | ~ (v13_waybel_0 @ X23 @ 
% 0.39/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24))))
% 0.39/0.56          | ~ (m1_subset_1 @ X23 @ 
% 0.39/0.56               (k1_zfmisc_1 @ 
% 0.39/0.56                (u1_struct_0 @ 
% 0.39/0.56                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24))))))
% 0.39/0.56          | ((X23)
% 0.39/0.56              = (k2_yellow19 @ X24 @ 
% 0.39/0.56                 (k3_yellow19 @ X24 @ (k2_struct_0 @ X24) @ X23)))
% 0.39/0.56          | ~ (l1_struct_0 @ X24)
% 0.39/0.56          | (v2_struct_0 @ X24))),
% 0.39/0.56      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 0.39/0.56  thf('121', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_A)
% 0.39/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.56        | ((sk_B)
% 0.39/0.56            = (k2_yellow19 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.39/0.56        | ~ (v13_waybel_0 @ sk_B @ 
% 0.39/0.56             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.39/0.56        | ~ (v2_waybel_0 @ sk_B @ 
% 0.39/0.56             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.39/0.56        | ~ (v1_subset_1 @ sk_B @ 
% 0.39/0.56             (u1_struct_0 @ 
% 0.39/0.56              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.39/0.56        | (v1_xboole_0 @ sk_B))),
% 0.39/0.56      inference('sup-', [status(thm)], ['114', '120'])).
% 0.39/0.56  thf('122', plain,
% 0.39/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.39/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.39/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.39/0.56  thf('123', plain,
% 0.39/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.39/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.39/0.56      inference('demod', [status(thm)], ['38', '39'])).
% 0.39/0.56  thf('124', plain,
% 0.39/0.56      ((v1_subset_1 @ sk_B @ 
% 0.39/0.56        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.39/0.56      inference('demod', [status(thm)], ['47', '48'])).
% 0.39/0.56  thf('125', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_A)
% 0.39/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.56        | ((sk_B)
% 0.39/0.56            = (k2_yellow19 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.39/0.56        | (v1_xboole_0 @ sk_B))),
% 0.39/0.56      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 0.39/0.56  thf('126', plain,
% 0.39/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.56        | (v1_xboole_0 @ sk_B)
% 0.39/0.56        | ((sk_B)
% 0.39/0.56            = (k2_yellow19 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.39/0.56        | (v2_struct_0 @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['113', '125'])).
% 0.39/0.56  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('128', plain,
% 0.39/0.56      (((v1_xboole_0 @ sk_B)
% 0.39/0.56        | ((sk_B)
% 0.39/0.56            = (k2_yellow19 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.39/0.56        | (v2_struct_0 @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['126', '127'])).
% 0.39/0.56  thf('129', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('130', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_A)
% 0.39/0.56        | ((sk_B)
% 0.39/0.56            = (k2_yellow19 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.39/0.56      inference('clc', [status(thm)], ['128', '129'])).
% 0.39/0.56  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('132', plain,
% 0.39/0.56      (((sk_B)
% 0.39/0.56         = (k2_yellow19 @ sk_A @ 
% 0.39/0.56            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.56      inference('clc', [status(thm)], ['130', '131'])).
% 0.39/0.56  thf('133', plain,
% 0.39/0.56      ((((sk_B)
% 0.39/0.56          = (k2_yellow19 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.39/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.56      inference('sup+', [status(thm)], ['112', '132'])).
% 0.39/0.56  thf('134', plain,
% 0.39/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.56        | ((sk_B)
% 0.39/0.56            = (k2_yellow19 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['111', '133'])).
% 0.39/0.56  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('136', plain,
% 0.39/0.56      (((sk_B)
% 0.39/0.56         = (k2_yellow19 @ sk_A @ 
% 0.39/0.56            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.56      inference('demod', [status(thm)], ['134', '135'])).
% 0.39/0.56  thf('137', plain,
% 0.39/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.39/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['110', '136'])).
% 0.39/0.56  thf('138', plain,
% 0.39/0.56      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['137'])).
% 0.39/0.56  thf('139', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.56  thf('140', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_B @ 
% 0.39/0.56        (k1_zfmisc_1 @ 
% 0.39/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.39/0.56      inference('demod', [status(thm)], ['17', '18'])).
% 0.39/0.56  thf('141', plain,
% 0.39/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.39/0.56          | (v1_xboole_0 @ X11)
% 0.39/0.56          | ~ (l1_struct_0 @ X12)
% 0.39/0.56          | (v2_struct_0 @ X12)
% 0.39/0.56          | (v1_xboole_0 @ X13)
% 0.39/0.56          | ~ (v2_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.39/0.56          | ~ (v13_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.39/0.56          | ~ (m1_subset_1 @ X13 @ 
% 0.39/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X11))))
% 0.39/0.56          | ~ (v2_struct_0 @ (k3_yellow19 @ X12 @ X11 @ X13)))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.39/0.56  thf('142', plain,
% 0.39/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.56  thf('143', plain,
% 0.39/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.56  thf('144', plain,
% 0.39/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.39/0.56  thf('145', plain,
% 0.39/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.39/0.56          | (v1_xboole_0 @ X11)
% 0.39/0.56          | ~ (l1_struct_0 @ X12)
% 0.39/0.56          | (v2_struct_0 @ X12)
% 0.39/0.56          | (v1_xboole_0 @ X13)
% 0.39/0.56          | ~ (v2_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.39/0.56          | ~ (v13_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.39/0.56          | ~ (m1_subset_1 @ X13 @ 
% 0.39/0.56               (k1_zfmisc_1 @ 
% 0.39/0.56                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X11)))))
% 0.39/0.56          | ~ (v2_struct_0 @ (k3_yellow19 @ X12 @ X11 @ X13)))),
% 0.39/0.56      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 0.39/0.56  thf('146', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | ~ (v13_waybel_0 @ sk_B @ 
% 0.39/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56          | ~ (v2_waybel_0 @ sk_B @ 
% 0.39/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56          | (v1_xboole_0 @ sk_B)
% 0.39/0.56          | (v2_struct_0 @ X0)
% 0.39/0.56          | ~ (l1_struct_0 @ X0)
% 0.39/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['140', '145'])).
% 0.39/0.56  thf('147', plain,
% 0.39/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.39/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('demod', [status(thm)], ['33', '34'])).
% 0.39/0.56  thf('148', plain,
% 0.39/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.39/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.39/0.56  thf('149', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | (v1_xboole_0 @ sk_B)
% 0.39/0.56          | (v2_struct_0 @ X0)
% 0.39/0.56          | ~ (l1_struct_0 @ X0)
% 0.39/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.39/0.56      inference('demod', [status(thm)], ['146', '147', '148'])).
% 0.39/0.56  thf('150', plain,
% 0.39/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | (v1_xboole_0 @ sk_B)
% 0.39/0.56        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['139', '149'])).
% 0.39/0.56  thf('151', plain,
% 0.39/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['138', '150'])).
% 0.39/0.56  thf('152', plain,
% 0.39/0.56      (((~ (l1_struct_0 @ sk_A)
% 0.39/0.56         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['151'])).
% 0.39/0.56  thf('153', plain,
% 0.39/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['3', '152'])).
% 0.39/0.56  thf('154', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('155', plain,
% 0.39/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))
% 0.39/0.56         <= (((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['153', '154'])).
% 0.39/0.56  thf('156', plain,
% 0.39/0.56      ((~ (r1_waybel_7 @ sk_A @ sk_B @ sk_C_1))
% 0.39/0.56         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('split', [status(esa)], ['0'])).
% 0.39/0.56  thf('157', plain,
% 0.39/0.56      ((((v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['155', '156'])).
% 0.39/0.56  thf('158', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('159', plain,
% 0.39/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.39/0.56         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('clc', [status(thm)], ['157', '158'])).
% 0.39/0.56  thf('160', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('161', plain,
% 0.39/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('clc', [status(thm)], ['159', '160'])).
% 0.39/0.56  thf(fc2_struct_0, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.56  thf('162', plain,
% 0.39/0.56      (![X9 : $i]:
% 0.39/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.39/0.56          | ~ (l1_struct_0 @ X9)
% 0.39/0.56          | (v2_struct_0 @ X9))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.39/0.56  thf('163', plain,
% 0.39/0.56      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['161', '162'])).
% 0.39/0.56  thf('164', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('165', plain,
% 0.39/0.56      ((~ (l1_struct_0 @ sk_A))
% 0.39/0.56         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('clc', [status(thm)], ['163', '164'])).
% 0.39/0.56  thf('166', plain,
% 0.39/0.56      ((~ (l1_pre_topc @ sk_A))
% 0.39/0.56         <= (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['2', '165'])).
% 0.39/0.56  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('168', plain,
% 0.39/0.56      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.39/0.56       ~
% 0.39/0.56       ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1))),
% 0.39/0.56      inference('demod', [status(thm)], ['166', '167'])).
% 0.39/0.56  thf('169', plain,
% 0.39/0.56      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.39/0.56       ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1))),
% 0.39/0.56      inference('split', [status(esa)], ['93'])).
% 0.39/0.56  thf('170', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.56  thf('171', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.56  thf('172', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.56  thf('173', plain,
% 0.39/0.56      (((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1))
% 0.39/0.56         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('split', [status(esa)], ['93'])).
% 0.39/0.56  thf('174', plain,
% 0.39/0.56      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56        | (v1_xboole_0 @ sk_B)
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['72', '73'])).
% 0.39/0.56  thf('175', plain,
% 0.39/0.56      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56        | (v1_xboole_0 @ sk_B)
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.39/0.56  thf('176', plain,
% 0.39/0.56      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.39/0.56         sk_A)
% 0.39/0.56        | (v1_xboole_0 @ sk_B)
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['88', '89'])).
% 0.39/0.56  thf('177', plain,
% 0.39/0.56      (((sk_B)
% 0.39/0.56         = (k2_yellow19 @ sk_A @ 
% 0.39/0.56            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.56      inference('demod', [status(thm)], ['134', '135'])).
% 0.39/0.56  thf('178', plain,
% 0.39/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.56         ((v2_struct_0 @ X20)
% 0.39/0.56          | ~ (v4_orders_2 @ X20)
% 0.39/0.56          | ~ (v7_waybel_0 @ X20)
% 0.39/0.56          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.39/0.56          | ~ (r1_waybel_7 @ X21 @ (k2_yellow19 @ X21 @ X20) @ X22)
% 0.39/0.56          | (r3_waybel_9 @ X21 @ X20 @ X22)
% 0.39/0.56          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.39/0.56          | ~ (l1_pre_topc @ X21)
% 0.39/0.56          | ~ (v2_pre_topc @ X21)
% 0.39/0.56          | (v2_struct_0 @ X21))),
% 0.39/0.56      inference('cnf', [status(esa)], [t12_yellow19])).
% 0.39/0.56  thf('179', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.39/0.56          | (v2_struct_0 @ sk_A)
% 0.39/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.56          | ~ (l1_waybel_0 @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.39/0.56          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['177', '178'])).
% 0.39/0.56  thf('180', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('181', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('182', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.39/0.56          | (v2_struct_0 @ sk_A)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.56          | ~ (l1_waybel_0 @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.39/0.56          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.56      inference('demod', [status(thm)], ['179', '180', '181'])).
% 0.39/0.56  thf('183', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | (v2_struct_0 @ sk_A)
% 0.39/0.56          | (v1_xboole_0 @ sk_B)
% 0.39/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | (v2_struct_0 @ sk_A)
% 0.39/0.56          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['176', '182'])).
% 0.39/0.56  thf('184', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.56          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | (v1_xboole_0 @ sk_B)
% 0.39/0.56          | (v2_struct_0 @ sk_A)
% 0.39/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['183'])).
% 0.39/0.56  thf('185', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | (v2_struct_0 @ sk_A)
% 0.39/0.56          | (v1_xboole_0 @ sk_B)
% 0.39/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | (v2_struct_0 @ sk_A)
% 0.39/0.56          | (v1_xboole_0 @ sk_B)
% 0.39/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['175', '184'])).
% 0.39/0.56  thf('186', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.56          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | (v1_xboole_0 @ sk_B)
% 0.39/0.56          | (v2_struct_0 @ sk_A)
% 0.39/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['185'])).
% 0.39/0.56  thf('187', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | (v2_struct_0 @ sk_A)
% 0.39/0.56          | (v1_xboole_0 @ sk_B)
% 0.39/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | (v2_struct_0 @ sk_A)
% 0.39/0.56          | (v1_xboole_0 @ sk_B)
% 0.39/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | ~ (r1_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['174', '186'])).
% 0.39/0.56  thf('188', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (r1_waybel_7 @ sk_A @ sk_B @ X0)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56          | (r3_waybel_9 @ sk_A @ 
% 0.39/0.56             (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.39/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56          | (v1_xboole_0 @ sk_B)
% 0.39/0.56          | (v2_struct_0 @ sk_A)
% 0.39/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['187'])).
% 0.39/0.56  thf('189', plain,
% 0.39/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | (r3_waybel_9 @ sk_A @ 
% 0.39/0.56            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C_1)
% 0.39/0.56         | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['173', '188'])).
% 0.39/0.56  thf('190', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('191', plain,
% 0.39/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | (r3_waybel_9 @ sk_A @ 
% 0.39/0.56            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))
% 0.39/0.56         <= (((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['189', '190'])).
% 0.39/0.56  thf('192', plain,
% 0.39/0.56      (![X7 : $i]:
% 0.39/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.56  thf('193', plain,
% 0.39/0.56      ((~ (r3_waybel_9 @ sk_A @ 
% 0.39/0.56           (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('split', [status(esa)], ['0'])).
% 0.39/0.56  thf('194', plain,
% 0.39/0.56      (((~ (r3_waybel_9 @ sk_A @ 
% 0.39/0.56            (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C_1)
% 0.39/0.56         | ~ (l1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['192', '193'])).
% 0.39/0.56  thf('195', plain,
% 0.39/0.56      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | ~ (l1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)) & 
% 0.39/0.56             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['191', '194'])).
% 0.39/0.56  thf('196', plain,
% 0.39/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)) & 
% 0.39/0.56             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['172', '195'])).
% 0.39/0.56  thf('197', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('198', plain,
% 0.39/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)) & 
% 0.39/0.56             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['196', '197'])).
% 0.39/0.56  thf('199', plain,
% 0.39/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | (v1_xboole_0 @ sk_B)
% 0.39/0.56        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['139', '149'])).
% 0.39/0.56  thf('200', plain,
% 0.39/0.56      ((((v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)) & 
% 0.39/0.56             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['198', '199'])).
% 0.39/0.56  thf('201', plain,
% 0.39/0.56      (((~ (l1_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)) & 
% 0.39/0.56             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['200'])).
% 0.39/0.56  thf('202', plain,
% 0.39/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)) & 
% 0.39/0.56             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['171', '201'])).
% 0.39/0.56  thf('203', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('204', plain,
% 0.39/0.56      ((((v1_xboole_0 @ sk_B)
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)) & 
% 0.39/0.56             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['202', '203'])).
% 0.39/0.56  thf('205', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('206', plain,
% 0.39/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)) & 
% 0.39/0.56             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('clc', [status(thm)], ['204', '205'])).
% 0.39/0.56  thf('207', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('208', plain,
% 0.39/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)) & 
% 0.39/0.56             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('clc', [status(thm)], ['206', '207'])).
% 0.39/0.56  thf('209', plain,
% 0.39/0.56      (![X9 : $i]:
% 0.39/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.39/0.56          | ~ (l1_struct_0 @ X9)
% 0.39/0.56          | (v2_struct_0 @ X9))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.39/0.56  thf('210', plain,
% 0.39/0.56      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)) & 
% 0.39/0.56             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['208', '209'])).
% 0.39/0.56  thf('211', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('212', plain,
% 0.39/0.56      ((~ (l1_struct_0 @ sk_A))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)) & 
% 0.39/0.56             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('clc', [status(thm)], ['210', '211'])).
% 0.39/0.56  thf('213', plain,
% 0.39/0.56      ((~ (l1_pre_topc @ sk_A))
% 0.39/0.56         <= (~
% 0.39/0.56             ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1)) & 
% 0.39/0.56             ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['170', '212'])).
% 0.39/0.56  thf('214', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('215', plain,
% 0.39/0.56      (~ ((r1_waybel_7 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.39/0.56       ((r3_waybel_9 @ sk_A @ 
% 0.39/0.56         (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_C_1))),
% 0.39/0.56      inference('demod', [status(thm)], ['213', '214'])).
% 0.39/0.56  thf('216', plain, ($false),
% 0.39/0.56      inference('sat_resolution*', [status(thm)], ['1', '168', '169', '215'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
