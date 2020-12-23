%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7ckKyHjJyE

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:53 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  323 ( 822 expanded)
%              Number of leaves         :   42 ( 272 expanded)
%              Depth                    :   39
%              Number of atoms          : 4332 (15113 expanded)
%              Number of equality atoms :   46 ( 194 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

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

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(t18_yellow19,conjecture,(
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
             => ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) )
              <=> ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) )).

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
               => ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) )
                <=> ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_yellow19])).

thf('0',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('15',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('17',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('23',plain,(
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

thf('24',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('25',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('27',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('28',plain,(
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
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
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
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('31',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('32',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('34',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('40',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('43',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('49',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('52',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','38','47','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','57'])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('65',plain,(
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

thf('66',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('67',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('68',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('69',plain,(
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
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('72',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','73'])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('81',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('83',plain,(
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

thf('84',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('85',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('86',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('87',plain,(
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
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('90',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['81','91'])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['97'])).

thf(t13_yellow19,axiom,(
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
             => ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) )
              <=> ( r2_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) )).

thf('99',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r2_hidden @ X22 @ ( k10_yellow_6 @ X21 @ X20 ) )
      | ( r2_waybel_7 @ X21 @ ( k2_yellow19 @ X21 @ X20 ) @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_waybel_7 @ sk_A @ ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C_1 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

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

thf('106',plain,(
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

thf('107',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('108',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('109',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('110',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('111',plain,(
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
    inference(demod,[status(thm)],['106','107','108','109','110'])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('114',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('115',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['100','101','102','103','123'])).

thf('125',plain,
    ( ( ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','124'])).

thf('126',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['95','125'])).

thf('127',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','127'])).

thf('129',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['78','129'])).

thf('131',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['77','131'])).

thf('133',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','133'])).

thf('135',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('140',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('141',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('142',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('143',plain,(
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

thf('144',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('145',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('146',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('147',plain,(
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
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['142','147'])).

thf('149',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('150',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['141','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['140','152'])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','155'])).

thf('157',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['138','156'])).

thf('158',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
   <= ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('163',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['4','163'])).

thf('165',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['3','165'])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['170','171'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('173',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('174',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','176'])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['97'])).

thf('181',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('182',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('183',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('184',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('185',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['97'])).

thf('186',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('187',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('188',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('189',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('190',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('191',plain,(
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
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('194',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['189','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['188','196'])).

thf('198',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['187','199'])).

thf('201',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['186','200'])).

thf('202',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('205',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('206',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('207',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('208',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('209',plain,(
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
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('212',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('213',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['210','211','212','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['207','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['206','215'])).

thf('217',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['205','218'])).

thf('220',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['204','219'])).

thf('221',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('224',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('225',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('226',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('227',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('228',plain,(
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
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    v13_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('231',plain,(
    v2_waybel_0 @ sk_B @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['226','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['225','233'])).

thf('235',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow19 @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['224','236'])).

thf('238',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['223','237'])).

thf('239',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['238','239'])).

thf('241',plain,
    ( sk_B
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('242',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r2_waybel_7 @ X21 @ ( k2_yellow19 @ X21 @ X20 ) @ X22 )
      | ( r2_hidden @ X22 @ ( k10_yellow_6 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow19])).

thf('243',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['243','244','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['240','246'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( v7_waybel_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['222','248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( v4_orders_2 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['203','250'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['251'])).

thf('253',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['185','252'])).

thf('254',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('256',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('257',plain,
    ( ( ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','155'])).

thf('259',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,
    ( ( ~ ( l1_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['259'])).

thf('261',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['184','260'])).

thf('262',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['261','262'])).

thf('264',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['263','264'])).

thf('266',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['265','266'])).

thf('268',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['183','267'])).

thf('269',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['182','268'])).

thf('270',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['269','270'])).

thf('272',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('273',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['271','272'])).

thf('274',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,
    ( ~ ( l1_struct_0 @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['273','274'])).

thf('276',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      & ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['181','275'])).

thf('277',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_C_1 @ ( k10_yellow_6 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['276','277'])).

thf('279',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','179','180','278'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7ckKyHjJyE
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:13:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 192 iterations in 0.087s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.37/0.56  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.56  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.37/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.56  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.37/0.56  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.37/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.56  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.56  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.37/0.56  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.37/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.37/0.56  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.37/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 0.37/0.56  thf(t18_yellow19, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.56             ( v1_subset_1 @
% 0.37/0.56               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.37/0.56             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.56             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.56             ( m1_subset_1 @
% 0.37/0.56               B @ 
% 0.37/0.56               ( k1_zfmisc_1 @
% 0.37/0.56                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56               ( ( r2_hidden @
% 0.37/0.56                   C @ 
% 0.37/0.56                   ( k10_yellow_6 @
% 0.37/0.56                     A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.37/0.56                 ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.56            ( l1_pre_topc @ A ) ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.56                ( v1_subset_1 @
% 0.37/0.56                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.37/0.56                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.56                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.56                ( m1_subset_1 @
% 0.37/0.56                  B @ 
% 0.37/0.56                  ( k1_zfmisc_1 @
% 0.37/0.56                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.56              ( ![C:$i]:
% 0.37/0.56                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56                  ( ( r2_hidden @
% 0.37/0.56                      C @ 
% 0.37/0.56                      ( k10_yellow_6 @
% 0.37/0.56                        A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) <=>
% 0.37/0.56                    ( r2_waybel_7 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t18_yellow19])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      ((~ (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56        | ~ (r2_hidden @ sk_C_1 @ 
% 0.37/0.56             (k10_yellow_6 @ sk_A @ 
% 0.37/0.56              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.37/0.56       ~
% 0.37/0.56       ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56         (k10_yellow_6 @ sk_A @ 
% 0.37/0.56          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf(dt_l1_pre_topc, axiom,
% 0.37/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.37/0.56  thf('2', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('3', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf(d3_struct_0, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X7 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('5', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('6', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('7', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf(d3_tarski, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.56  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.37/0.56  thf(t3_subset, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X4 : $i, X6 : $i]:
% 0.37/0.56         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.56  thf('13', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.56  thf('14', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X7 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ 
% 0.37/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(d2_yellow_1, axiom,
% 0.37/0.56    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (((m1_subset_1 @ sk_B @ 
% 0.37/0.56         (k1_zfmisc_1 @ 
% 0.37/0.56          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup+', [status(thm)], ['15', '18'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (m1_subset_1 @ sk_B @ 
% 0.37/0.56           (k1_zfmisc_1 @ 
% 0.37/0.56            (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['14', '19'])).
% 0.37/0.56  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf(fc5_yellow19, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.37/0.56         ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.37/0.56         ( ~( v1_xboole_0 @ C ) ) & 
% 0.37/0.56         ( v1_subset_1 @ C @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) & 
% 0.37/0.56         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.56         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.56         ( m1_subset_1 @
% 0.37/0.56           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.37/0.56       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.37/0.56         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.37/0.56         ( v7_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) ))).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.56          | (v1_xboole_0 @ X17)
% 0.37/0.56          | ~ (l1_struct_0 @ X18)
% 0.37/0.56          | (v2_struct_0 @ X18)
% 0.37/0.56          | (v1_xboole_0 @ X19)
% 0.37/0.56          | ~ (v1_subset_1 @ X19 @ (u1_struct_0 @ (k3_yellow_1 @ X17)))
% 0.37/0.56          | ~ (v2_waybel_0 @ X19 @ (k3_yellow_1 @ X17))
% 0.37/0.56          | ~ (v13_waybel_0 @ X19 @ (k3_yellow_1 @ X17))
% 0.37/0.56          | ~ (m1_subset_1 @ X19 @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X17))))
% 0.37/0.56          | (v7_waybel_0 @ (k3_yellow19 @ X18 @ X17 @ X19)))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc5_yellow19])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.56          | (v1_xboole_0 @ X17)
% 0.37/0.56          | ~ (l1_struct_0 @ X18)
% 0.37/0.56          | (v2_struct_0 @ X18)
% 0.37/0.56          | (v1_xboole_0 @ X19)
% 0.37/0.56          | ~ (v1_subset_1 @ X19 @ 
% 0.37/0.56               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X17))))
% 0.37/0.56          | ~ (v2_waybel_0 @ X19 @ (k3_lattice3 @ (k1_lattice3 @ X17)))
% 0.37/0.56          | ~ (v13_waybel_0 @ X19 @ (k3_lattice3 @ (k1_lattice3 @ X17)))
% 0.37/0.56          | ~ (m1_subset_1 @ X19 @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X17)))))
% 0.37/0.56          | (v7_waybel_0 @ (k3_yellow19 @ X18 @ X17 @ X19)))),
% 0.37/0.56      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56          | ~ (v1_subset_1 @ sk_B @ 
% 0.37/0.56               (u1_struct_0 @ 
% 0.37/0.56                (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['22', '28'])).
% 0.37/0.56  thf('30', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X7 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      ((v13_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (((v13_waybel_0 @ sk_B @ 
% 0.37/0.56         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup+', [status(thm)], ['31', '34'])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v13_waybel_0 @ sk_B @ 
% 0.37/0.56           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['30', '35'])).
% 0.37/0.56  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.56  thf('39', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (![X7 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      ((v2_waybel_0 @ sk_B @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (((v2_waybel_0 @ sk_B @ 
% 0.37/0.56         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup+', [status(thm)], ['40', '43'])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v2_waybel_0 @ sk_B @ 
% 0.37/0.56           (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['39', '44'])).
% 0.37/0.56  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('48', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      (![X7 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      ((v1_subset_1 @ sk_B @ 
% 0.37/0.56        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      ((v1_subset_1 @ sk_B @ 
% 0.37/0.56        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.56      inference('demod', [status(thm)], ['50', '51'])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (((v1_subset_1 @ sk_B @ 
% 0.37/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup+', [status(thm)], ['49', '52'])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v1_subset_1 @ sk_B @ 
% 0.37/0.56           (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['48', '53'])).
% 0.37/0.56  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      ((v1_subset_1 @ sk_B @ 
% 0.37/0.56        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.56      inference('demod', [status(thm)], ['54', '55'])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('demod', [status(thm)], ['29', '38', '47', '56'])).
% 0.37/0.56  thf('58', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['13', '57'])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['7', '58'])).
% 0.37/0.56  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.37/0.56  thf('62', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('63', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.56  thf('64', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf(fc4_yellow19, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.37/0.56         ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.37/0.56         ( ~( v1_xboole_0 @ C ) ) & 
% 0.37/0.56         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.56         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.56         ( m1_subset_1 @
% 0.37/0.56           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.37/0.56       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.37/0.56         ( v3_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.37/0.56         ( v4_orders_2 @ ( k3_yellow19 @ A @ B @ C ) ) & 
% 0.37/0.56         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.37/0.56  thf('65', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.37/0.56          | (v1_xboole_0 @ X14)
% 0.37/0.56          | ~ (l1_struct_0 @ X15)
% 0.37/0.56          | (v2_struct_0 @ X15)
% 0.37/0.56          | (v1_xboole_0 @ X16)
% 0.37/0.56          | ~ (v2_waybel_0 @ X16 @ (k3_yellow_1 @ X14))
% 0.37/0.56          | ~ (v13_waybel_0 @ X16 @ (k3_yellow_1 @ X14))
% 0.37/0.56          | ~ (m1_subset_1 @ X16 @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X14))))
% 0.37/0.56          | (v4_orders_2 @ (k3_yellow19 @ X15 @ X14 @ X16)))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc4_yellow19])).
% 0.37/0.56  thf('66', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('67', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('68', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('69', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.37/0.56          | (v1_xboole_0 @ X14)
% 0.37/0.56          | ~ (l1_struct_0 @ X15)
% 0.37/0.56          | (v2_struct_0 @ X15)
% 0.37/0.56          | (v1_xboole_0 @ X16)
% 0.37/0.56          | ~ (v2_waybel_0 @ X16 @ (k3_lattice3 @ (k1_lattice3 @ X14)))
% 0.37/0.56          | ~ (v13_waybel_0 @ X16 @ (k3_lattice3 @ (k1_lattice3 @ X14)))
% 0.37/0.56          | ~ (m1_subset_1 @ X16 @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X14)))))
% 0.37/0.56          | (v4_orders_2 @ (k3_yellow19 @ X15 @ X14 @ X16)))),
% 0.37/0.56      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.37/0.56  thf('70', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['64', '69'])).
% 0.37/0.56  thf('71', plain,
% 0.37/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.56  thf('72', plain,
% 0.37/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('73', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.37/0.56  thf('74', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['63', '73'])).
% 0.37/0.56  thf('75', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['62', '74'])).
% 0.37/0.56  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('77', plain,
% 0.37/0.56      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.56  thf('78', plain,
% 0.37/0.56      (![X7 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('79', plain,
% 0.37/0.56      (![X7 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('80', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('81', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.56  thf('82', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.56      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf(dt_k3_yellow19, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.37/0.56         ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.37/0.56         ( ~( v1_xboole_0 @ C ) ) & 
% 0.37/0.56         ( v2_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.56         ( v13_waybel_0 @ C @ ( k3_yellow_1 @ B ) ) & 
% 0.37/0.56         ( m1_subset_1 @
% 0.37/0.56           C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ B ) ) ) ) ) =>
% 0.37/0.56       ( ( ~( v2_struct_0 @ ( k3_yellow19 @ A @ B @ C ) ) ) & 
% 0.37/0.56         ( v6_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) & 
% 0.37/0.56         ( l1_waybel_0 @ ( k3_yellow19 @ A @ B @ C ) @ A ) ) ))).
% 0.37/0.56  thf('83', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.56          | (v1_xboole_0 @ X11)
% 0.37/0.56          | ~ (l1_struct_0 @ X12)
% 0.37/0.56          | (v2_struct_0 @ X12)
% 0.37/0.56          | (v1_xboole_0 @ X13)
% 0.37/0.56          | ~ (v2_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.37/0.56          | ~ (v13_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.37/0.56          | ~ (m1_subset_1 @ X13 @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X11))))
% 0.37/0.56          | (l1_waybel_0 @ (k3_yellow19 @ X12 @ X11 @ X13) @ X12))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.37/0.56  thf('84', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('85', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('86', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('87', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.56          | (v1_xboole_0 @ X11)
% 0.37/0.56          | ~ (l1_struct_0 @ X12)
% 0.37/0.56          | (v2_struct_0 @ X12)
% 0.37/0.56          | (v1_xboole_0 @ X13)
% 0.37/0.56          | ~ (v2_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.37/0.56          | ~ (v13_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.37/0.56          | ~ (m1_subset_1 @ X13 @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X11)))))
% 0.37/0.56          | (l1_waybel_0 @ (k3_yellow19 @ X12 @ X11 @ X13) @ X12))),
% 0.37/0.56      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 0.37/0.56  thf('88', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.56          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['82', '87'])).
% 0.37/0.56  thf('89', plain,
% 0.37/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.56  thf('90', plain,
% 0.37/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('91', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.37/0.56  thf('92', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.56           sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['81', '91'])).
% 0.37/0.56  thf('93', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.56           sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['80', '92'])).
% 0.37/0.56  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('95', plain,
% 0.37/0.56      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.56         sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['93', '94'])).
% 0.37/0.56  thf('96', plain,
% 0.37/0.56      (![X7 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('97', plain,
% 0.37/0.56      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56        | (r2_hidden @ sk_C_1 @ 
% 0.37/0.56           (k10_yellow_6 @ sk_A @ 
% 0.37/0.56            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('98', plain,
% 0.37/0.56      (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56         (k10_yellow_6 @ sk_A @ 
% 0.37/0.56          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('split', [status(esa)], ['97'])).
% 0.37/0.56  thf(t13_yellow19, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.37/0.56             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) <=>
% 0.37/0.56                 ( r2_waybel_7 @ A @ ( k2_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.37/0.56  thf('99', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.56         ((v2_struct_0 @ X20)
% 0.37/0.56          | ~ (v4_orders_2 @ X20)
% 0.37/0.56          | ~ (v7_waybel_0 @ X20)
% 0.37/0.56          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.37/0.56          | ~ (r2_hidden @ X22 @ (k10_yellow_6 @ X21 @ X20))
% 0.37/0.56          | (r2_waybel_7 @ X21 @ (k2_yellow19 @ X21 @ X20) @ X22)
% 0.37/0.56          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.37/0.56          | ~ (l1_pre_topc @ X21)
% 0.37/0.56          | ~ (v2_pre_topc @ X21)
% 0.37/0.56          | (v2_struct_0 @ X21))),
% 0.37/0.56      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.37/0.56  thf('100', plain,
% 0.37/0.56      ((((v2_struct_0 @ sk_A)
% 0.37/0.56         | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56         | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ 
% 0.37/0.56            (k2_yellow19 @ sk_A @ 
% 0.37/0.56             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.37/0.56            sk_C_1)
% 0.37/0.56         | ~ (l1_waybel_0 @ 
% 0.37/0.56              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.37/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['98', '99'])).
% 0.37/0.56  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('103', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('104', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('105', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf(t15_yellow19, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.56             ( v1_subset_1 @
% 0.37/0.56               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.37/0.56             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.56             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.37/0.56             ( m1_subset_1 @
% 0.37/0.56               B @ 
% 0.37/0.56               ( k1_zfmisc_1 @
% 0.37/0.56                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.37/0.56           ( ( B ) =
% 0.37/0.56             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.37/0.56  thf('106', plain,
% 0.37/0.56      (![X23 : $i, X24 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ X23)
% 0.37/0.56          | ~ (v1_subset_1 @ X23 @ 
% 0.37/0.56               (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X24))))
% 0.37/0.56          | ~ (v2_waybel_0 @ X23 @ (k3_yellow_1 @ (k2_struct_0 @ X24)))
% 0.37/0.56          | ~ (v13_waybel_0 @ X23 @ (k3_yellow_1 @ (k2_struct_0 @ X24)))
% 0.37/0.56          | ~ (m1_subset_1 @ X23 @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X24)))))
% 0.37/0.56          | ((X23)
% 0.37/0.56              = (k2_yellow19 @ X24 @ 
% 0.37/0.56                 (k3_yellow19 @ X24 @ (k2_struct_0 @ X24) @ X23)))
% 0.37/0.56          | ~ (l1_struct_0 @ X24)
% 0.37/0.56          | (v2_struct_0 @ X24))),
% 0.37/0.56      inference('cnf', [status(esa)], [t15_yellow19])).
% 0.37/0.56  thf('107', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('108', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('109', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('110', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('111', plain,
% 0.37/0.56      (![X23 : $i, X24 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ X23)
% 0.37/0.56          | ~ (v1_subset_1 @ X23 @ 
% 0.37/0.56               (u1_struct_0 @ 
% 0.37/0.56                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24)))))
% 0.37/0.56          | ~ (v2_waybel_0 @ X23 @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24))))
% 0.37/0.56          | ~ (v13_waybel_0 @ X23 @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24))))
% 0.37/0.56          | ~ (m1_subset_1 @ X23 @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (u1_struct_0 @ 
% 0.37/0.56                 (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X24))))))
% 0.37/0.56          | ((X23)
% 0.37/0.56              = (k2_yellow19 @ X24 @ 
% 0.37/0.56                 (k3_yellow19 @ X24 @ (k2_struct_0 @ X24) @ X23)))
% 0.37/0.56          | ~ (l1_struct_0 @ X24)
% 0.37/0.56          | (v2_struct_0 @ X24))),
% 0.37/0.56      inference('demod', [status(thm)], ['106', '107', '108', '109', '110'])).
% 0.37/0.56  thf('112', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56        | ((sk_B)
% 0.37/0.56            = (k2_yellow19 @ sk_A @ 
% 0.37/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.56        | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.56             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56        | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.56             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56        | ~ (v1_subset_1 @ sk_B @ 
% 0.37/0.56             (u1_struct_0 @ 
% 0.37/0.56              (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.37/0.56        | (v1_xboole_0 @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['105', '111'])).
% 0.37/0.56  thf('113', plain,
% 0.37/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.56  thf('114', plain,
% 0.37/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.56  thf('115', plain,
% 0.37/0.56      ((v1_subset_1 @ sk_B @ 
% 0.37/0.56        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.56      inference('demod', [status(thm)], ['50', '51'])).
% 0.37/0.56  thf('116', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56        | ((sk_B)
% 0.37/0.56            = (k2_yellow19 @ sk_A @ 
% 0.37/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.56        | (v1_xboole_0 @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 0.37/0.56  thf('117', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | ((sk_B)
% 0.37/0.56            = (k2_yellow19 @ sk_A @ 
% 0.37/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.56        | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['104', '116'])).
% 0.37/0.56  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('119', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_B)
% 0.37/0.56        | ((sk_B)
% 0.37/0.56            = (k2_yellow19 @ sk_A @ 
% 0.37/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.56        | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['117', '118'])).
% 0.37/0.56  thf('120', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('121', plain,
% 0.37/0.56      (((v2_struct_0 @ sk_A)
% 0.37/0.56        | ((sk_B)
% 0.37/0.56            = (k2_yellow19 @ sk_A @ 
% 0.37/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.56      inference('clc', [status(thm)], ['119', '120'])).
% 0.37/0.56  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('123', plain,
% 0.37/0.56      (((sk_B)
% 0.37/0.56         = (k2_yellow19 @ sk_A @ 
% 0.37/0.56            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.56      inference('clc', [status(thm)], ['121', '122'])).
% 0.37/0.56  thf('124', plain,
% 0.37/0.56      ((((v2_struct_0 @ sk_A)
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | ~ (l1_waybel_0 @ 
% 0.37/0.56              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.37/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('demod', [status(thm)], ['100', '101', '102', '103', '123'])).
% 0.37/0.56  thf('125', plain,
% 0.37/0.56      (((~ (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.56            sk_A)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | (v2_struct_0 @ sk_A)))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['96', '124'])).
% 0.37/0.56  thf('126', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['95', '125'])).
% 0.37/0.56  thf('127', plain,
% 0.37/0.56      (((~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['126'])).
% 0.37/0.56  thf('128', plain,
% 0.37/0.56      (((~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['79', '127'])).
% 0.37/0.56  thf('129', plain,
% 0.37/0.56      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['128'])).
% 0.37/0.56  thf('130', plain,
% 0.37/0.56      (((~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['78', '129'])).
% 0.37/0.56  thf('131', plain,
% 0.37/0.56      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['130'])).
% 0.37/0.56  thf('132', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['77', '131'])).
% 0.37/0.56  thf('133', plain,
% 0.37/0.56      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['132'])).
% 0.37/0.56  thf('134', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['61', '133'])).
% 0.37/0.56  thf('135', plain,
% 0.37/0.56      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['134'])).
% 0.37/0.56  thf('136', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '135'])).
% 0.37/0.56  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('138', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('demod', [status(thm)], ['136', '137'])).
% 0.37/0.56  thf('139', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.56  thf('140', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('141', plain,
% 0.37/0.56      (![X7 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('142', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('143', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.56          | (v1_xboole_0 @ X11)
% 0.37/0.56          | ~ (l1_struct_0 @ X12)
% 0.37/0.56          | (v2_struct_0 @ X12)
% 0.37/0.56          | (v1_xboole_0 @ X13)
% 0.37/0.56          | ~ (v2_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.37/0.56          | ~ (v13_waybel_0 @ X13 @ (k3_yellow_1 @ X11))
% 0.37/0.56          | ~ (m1_subset_1 @ X13 @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X11))))
% 0.37/0.56          | ~ (v2_struct_0 @ (k3_yellow19 @ X12 @ X11 @ X13)))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k3_yellow19])).
% 0.37/0.56  thf('144', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('145', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('146', plain,
% 0.37/0.56      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k3_lattice3 @ (k1_lattice3 @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.37/0.56  thf('147', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.56          | (v1_xboole_0 @ X11)
% 0.37/0.56          | ~ (l1_struct_0 @ X12)
% 0.37/0.56          | (v2_struct_0 @ X12)
% 0.37/0.56          | (v1_xboole_0 @ X13)
% 0.37/0.56          | ~ (v2_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.37/0.56          | ~ (v13_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.37/0.56          | ~ (m1_subset_1 @ X13 @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X11)))))
% 0.37/0.56          | ~ (v2_struct_0 @ (k3_yellow19 @ X12 @ X11 @ X13)))),
% 0.37/0.56      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 0.37/0.56  thf('148', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['142', '147'])).
% 0.37/0.56  thf('149', plain,
% 0.37/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.56  thf('150', plain,
% 0.37/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.56  thf('151', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.37/0.56  thf('152', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.37/0.56          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['141', '151'])).
% 0.37/0.56  thf('153', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | ~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['140', '152'])).
% 0.37/0.56  thf('154', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('155', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v2_struct_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('demod', [status(thm)], ['153', '154'])).
% 0.37/0.56  thf('156', plain,
% 0.37/0.56      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['139', '155'])).
% 0.37/0.56  thf('157', plain,
% 0.37/0.56      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['138', '156'])).
% 0.37/0.56  thf('158', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['157'])).
% 0.37/0.56  thf('159', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.37/0.56         | (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '158'])).
% 0.37/0.56  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('161', plain,
% 0.37/0.56      ((((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56         <= (((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('demod', [status(thm)], ['159', '160'])).
% 0.37/0.56  thf('162', plain,
% 0.37/0.56      ((~ (r2_waybel_7 @ sk_A @ sk_B @ sk_C_1))
% 0.37/0.56         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('163', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)))
% 0.37/0.56         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['161', '162'])).
% 0.37/0.56  thf('164', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup+', [status(thm)], ['4', '163'])).
% 0.37/0.56  thf('165', plain,
% 0.37/0.56      ((((v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['164'])).
% 0.37/0.56  thf('166', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)))
% 0.37/0.56         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '165'])).
% 0.37/0.56  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('168', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)))
% 0.37/0.56         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('demod', [status(thm)], ['166', '167'])).
% 0.37/0.56  thf('169', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('170', plain,
% 0.37/0.56      ((((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('clc', [status(thm)], ['168', '169'])).
% 0.37/0.56  thf('171', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('172', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('clc', [status(thm)], ['170', '171'])).
% 0.37/0.56  thf(fc2_struct_0, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.56  thf('173', plain,
% 0.37/0.56      (![X9 : $i]:
% 0.37/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.37/0.56          | ~ (l1_struct_0 @ X9)
% 0.37/0.56          | (v2_struct_0 @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.37/0.56  thf('174', plain,
% 0.37/0.56      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.37/0.56         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['172', '173'])).
% 0.37/0.56  thf('175', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('176', plain,
% 0.37/0.56      ((~ (l1_struct_0 @ sk_A))
% 0.37/0.56         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('clc', [status(thm)], ['174', '175'])).
% 0.37/0.56  thf('177', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A))
% 0.37/0.56         <= (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '176'])).
% 0.37/0.56  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('179', plain,
% 0.37/0.56      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.37/0.56       ~
% 0.37/0.56       ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56         (k10_yellow_6 @ sk_A @ 
% 0.37/0.56          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['177', '178'])).
% 0.37/0.56  thf('180', plain,
% 0.37/0.56      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.37/0.56       ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56         (k10_yellow_6 @ sk_A @ 
% 0.37/0.56          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.56      inference('split', [status(esa)], ['97'])).
% 0.37/0.56  thf('181', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('182', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('183', plain,
% 0.37/0.56      (![X7 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('184', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('185', plain,
% 0.37/0.56      (((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1))
% 0.37/0.56         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('split', [status(esa)], ['97'])).
% 0.37/0.56  thf('186', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('187', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.56  thf('188', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('189', plain,
% 0.37/0.56      (![X7 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('190', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('191', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.37/0.56          | (v1_xboole_0 @ X14)
% 0.37/0.56          | ~ (l1_struct_0 @ X15)
% 0.37/0.56          | (v2_struct_0 @ X15)
% 0.37/0.56          | (v1_xboole_0 @ X16)
% 0.37/0.56          | ~ (v2_waybel_0 @ X16 @ (k3_lattice3 @ (k1_lattice3 @ X14)))
% 0.37/0.56          | ~ (v13_waybel_0 @ X16 @ (k3_lattice3 @ (k1_lattice3 @ X14)))
% 0.37/0.56          | ~ (m1_subset_1 @ X16 @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X14)))))
% 0.37/0.56          | (v4_orders_2 @ (k3_yellow19 @ X15 @ X14 @ X16)))),
% 0.37/0.56      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.37/0.56  thf('192', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['190', '191'])).
% 0.37/0.56  thf('193', plain,
% 0.37/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.56  thf('194', plain,
% 0.37/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.56  thf('195', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('demod', [status(thm)], ['192', '193', '194'])).
% 0.37/0.56  thf('196', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.37/0.56          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['189', '195'])).
% 0.37/0.56  thf('197', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | (v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['188', '196'])).
% 0.37/0.56  thf('198', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('199', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v4_orders_2 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('demod', [status(thm)], ['197', '198'])).
% 0.37/0.56  thf('200', plain,
% 0.37/0.56      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['187', '199'])).
% 0.37/0.56  thf('201', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['186', '200'])).
% 0.37/0.56  thf('202', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('203', plain,
% 0.37/0.56      (((v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['201', '202'])).
% 0.37/0.56  thf('204', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('205', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.56  thf('206', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('207', plain,
% 0.37/0.56      (![X7 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('208', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('209', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.56          | (v1_xboole_0 @ X17)
% 0.37/0.56          | ~ (l1_struct_0 @ X18)
% 0.37/0.56          | (v2_struct_0 @ X18)
% 0.37/0.56          | (v1_xboole_0 @ X19)
% 0.37/0.56          | ~ (v1_subset_1 @ X19 @ 
% 0.37/0.56               (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X17))))
% 0.37/0.56          | ~ (v2_waybel_0 @ X19 @ (k3_lattice3 @ (k1_lattice3 @ X17)))
% 0.37/0.56          | ~ (v13_waybel_0 @ X19 @ (k3_lattice3 @ (k1_lattice3 @ X17)))
% 0.37/0.56          | ~ (m1_subset_1 @ X19 @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X17)))))
% 0.37/0.56          | (v7_waybel_0 @ (k3_yellow19 @ X18 @ X17 @ X19)))),
% 0.37/0.56      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.37/0.56  thf('210', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56          | ~ (v1_subset_1 @ sk_B @ 
% 0.37/0.56               (u1_struct_0 @ 
% 0.37/0.56                (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['208', '209'])).
% 0.37/0.56  thf('211', plain,
% 0.37/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.56  thf('212', plain,
% 0.37/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.56  thf('213', plain,
% 0.37/0.56      ((v1_subset_1 @ sk_B @ 
% 0.37/0.56        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.56      inference('demod', [status(thm)], ['50', '51'])).
% 0.37/0.56  thf('214', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('demod', [status(thm)], ['210', '211', '212', '213'])).
% 0.37/0.56  thf('215', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.37/0.56          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['207', '214'])).
% 0.37/0.56  thf('216', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | (v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['206', '215'])).
% 0.37/0.56  thf('217', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('218', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v7_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('demod', [status(thm)], ['216', '217'])).
% 0.37/0.56  thf('219', plain,
% 0.37/0.56      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['205', '218'])).
% 0.37/0.56  thf('220', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['204', '219'])).
% 0.37/0.56  thf('221', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('222', plain,
% 0.37/0.56      (((v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['220', '221'])).
% 0.37/0.56  thf('223', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('224', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.56  thf('225', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('226', plain,
% 0.37/0.56      (![X7 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('227', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('228', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.37/0.56          | (v1_xboole_0 @ X11)
% 0.37/0.56          | ~ (l1_struct_0 @ X12)
% 0.37/0.56          | (v2_struct_0 @ X12)
% 0.37/0.56          | (v1_xboole_0 @ X13)
% 0.37/0.56          | ~ (v2_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.37/0.56          | ~ (v13_waybel_0 @ X13 @ (k3_lattice3 @ (k1_lattice3 @ X11)))
% 0.37/0.56          | ~ (m1_subset_1 @ X13 @ 
% 0.37/0.56               (k1_zfmisc_1 @ 
% 0.37/0.56                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X11)))))
% 0.37/0.56          | (l1_waybel_0 @ (k3_yellow19 @ X12 @ X11 @ X13) @ X12))),
% 0.37/0.56      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 0.37/0.56  thf('229', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.56          | ~ (v13_waybel_0 @ sk_B @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56          | ~ (v2_waybel_0 @ sk_B @ 
% 0.37/0.56               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['227', '228'])).
% 0.37/0.56  thf('230', plain,
% 0.37/0.56      ((v13_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.56  thf('231', plain,
% 0.37/0.56      ((v2_waybel_0 @ sk_B @ 
% 0.37/0.56        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.56  thf('232', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('demod', [status(thm)], ['229', '230', '231'])).
% 0.37/0.56  thf('233', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.37/0.56          | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.56             X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['226', '232'])).
% 0.37/0.56  thf('234', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | (l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.56             X0)
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['225', '233'])).
% 0.37/0.56  thf('235', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('236', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((l1_waybel_0 @ (k3_yellow19 @ X0 @ (k2_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.37/0.56      inference('demod', [status(thm)], ['234', '235'])).
% 0.37/0.56  thf('237', plain,
% 0.37/0.56      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.56           sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['224', '236'])).
% 0.37/0.56  thf('238', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.56           sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['223', '237'])).
% 0.37/0.56  thf('239', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('240', plain,
% 0.37/0.56      (((l1_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.56         sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['238', '239'])).
% 0.37/0.56  thf('241', plain,
% 0.37/0.56      (((sk_B)
% 0.37/0.56         = (k2_yellow19 @ sk_A @ 
% 0.37/0.56            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.56      inference('clc', [status(thm)], ['121', '122'])).
% 0.37/0.56  thf('242', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.56         ((v2_struct_0 @ X20)
% 0.37/0.56          | ~ (v4_orders_2 @ X20)
% 0.37/0.56          | ~ (v7_waybel_0 @ X20)
% 0.37/0.56          | ~ (l1_waybel_0 @ X20 @ X21)
% 0.37/0.56          | ~ (r2_waybel_7 @ X21 @ (k2_yellow19 @ X21 @ X20) @ X22)
% 0.37/0.56          | (r2_hidden @ X22 @ (k10_yellow_6 @ X21 @ X20))
% 0.37/0.56          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.37/0.56          | ~ (l1_pre_topc @ X21)
% 0.37/0.56          | ~ (v2_pre_topc @ X21)
% 0.37/0.56          | (v2_struct_0 @ X21))),
% 0.37/0.56      inference('cnf', [status(esa)], [t13_yellow19])).
% 0.37/0.56  thf('243', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.37/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | (r2_hidden @ X0 @ 
% 0.37/0.56             (k10_yellow_6 @ sk_A @ 
% 0.37/0.56              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.56          | ~ (l1_waybel_0 @ 
% 0.37/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.37/0.56          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['241', '242'])).
% 0.37/0.56  thf('244', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('245', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('246', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | (r2_hidden @ X0 @ 
% 0.37/0.56             (k10_yellow_6 @ sk_A @ 
% 0.37/0.56              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.56          | ~ (l1_waybel_0 @ 
% 0.37/0.56               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.37/0.56          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['243', '244', '245'])).
% 0.37/0.56  thf('247', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (r2_hidden @ X0 @ 
% 0.37/0.56             (k10_yellow_6 @ sk_A @ 
% 0.37/0.56              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['240', '246'])).
% 0.37/0.56  thf('248', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | (r2_hidden @ X0 @ 
% 0.37/0.56             (k10_yellow_6 @ sk_A @ 
% 0.37/0.56              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.56          | ~ (v7_waybel_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['247'])).
% 0.37/0.56  thf('249', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (r2_hidden @ X0 @ 
% 0.37/0.56             (k10_yellow_6 @ sk_A @ 
% 0.37/0.56              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['222', '248'])).
% 0.37/0.56  thf('250', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | (r2_hidden @ X0 @ 
% 0.37/0.56             (k10_yellow_6 @ sk_A @ 
% 0.37/0.56              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.56          | ~ (v4_orders_2 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['249'])).
% 0.37/0.56  thf('251', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (r2_hidden @ X0 @ 
% 0.37/0.56             (k10_yellow_6 @ sk_A @ 
% 0.37/0.56              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ~ (r2_waybel_7 @ sk_A @ sk_B @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['203', '250'])).
% 0.37/0.56  thf('252', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r2_waybel_7 @ sk_A @ sk_B @ X0)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | (r2_hidden @ X0 @ 
% 0.37/0.56             (k10_yellow_6 @ sk_A @ 
% 0.37/0.56              (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.56          | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56          | (v1_xboole_0 @ sk_B)
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['251'])).
% 0.37/0.56  thf('253', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | (r2_hidden @ sk_C_1 @ 
% 0.37/0.56            (k10_yellow_6 @ sk_A @ 
% 0.37/0.56             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.37/0.56         | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['185', '252'])).
% 0.37/0.56  thf('254', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('255', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | (r2_hidden @ sk_C_1 @ 
% 0.37/0.56            (k10_yellow_6 @ sk_A @ 
% 0.37/0.56             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.37/0.56         <= (((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['253', '254'])).
% 0.37/0.56  thf('256', plain,
% 0.37/0.56      ((~ (r2_hidden @ sk_C_1 @ 
% 0.37/0.56           (k10_yellow_6 @ sk_A @ 
% 0.37/0.56            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('257', plain,
% 0.37/0.56      ((((v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['255', '256'])).
% 0.37/0.56  thf('258', plain,
% 0.37/0.56      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ sk_B)
% 0.37/0.56        | ~ (v2_struct_0 @ (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['139', '155'])).
% 0.37/0.56  thf('259', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['257', '258'])).
% 0.37/0.56  thf('260', plain,
% 0.37/0.56      (((~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['259'])).
% 0.37/0.56  thf('261', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['184', '260'])).
% 0.37/0.56  thf('262', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('263', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56         | (v2_struct_0 @ sk_A)
% 0.37/0.56         | (v1_xboole_0 @ sk_B)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['261', '262'])).
% 0.37/0.56  thf('264', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('265', plain,
% 0.37/0.56      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('clc', [status(thm)], ['263', '264'])).
% 0.37/0.56  thf('266', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('267', plain,
% 0.37/0.56      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('clc', [status(thm)], ['265', '266'])).
% 0.37/0.56  thf('268', plain,
% 0.37/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['183', '267'])).
% 0.37/0.56  thf('269', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['182', '268'])).
% 0.37/0.56  thf('270', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('271', plain,
% 0.37/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['269', '270'])).
% 0.37/0.56  thf('272', plain,
% 0.37/0.56      (![X9 : $i]:
% 0.37/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.37/0.56          | ~ (l1_struct_0 @ X9)
% 0.37/0.56          | (v2_struct_0 @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.37/0.56  thf('273', plain,
% 0.37/0.56      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['271', '272'])).
% 0.37/0.56  thf('274', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('275', plain,
% 0.37/0.56      ((~ (l1_struct_0 @ sk_A))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('clc', [status(thm)], ['273', '274'])).
% 0.37/0.56  thf('276', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A))
% 0.37/0.56         <= (~
% 0.37/0.56             ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56               (k10_yellow_6 @ sk_A @ 
% 0.37/0.56                (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B)))) & 
% 0.37/0.56             ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['181', '275'])).
% 0.37/0.56  thf('277', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('278', plain,
% 0.37/0.56      (~ ((r2_waybel_7 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.37/0.56       ((r2_hidden @ sk_C_1 @ 
% 0.37/0.56         (k10_yellow_6 @ sk_A @ 
% 0.37/0.56          (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['276', '277'])).
% 0.37/0.56  thf('279', plain, ($false),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['1', '179', '180', '278'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
