%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LNlbpmUOQL

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:38 EST 2020

% Result     : Theorem 5.26s
% Output     : Refutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 609 expanded)
%              Number of leaves         :   36 ( 184 expanded)
%              Depth                    :   25
%              Number of atoms          : 2380 (11107 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_yellow19_type,type,(
    k1_yellow19: $i > $i > $i )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t4_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
             => ( ( r2_waybel_7 @ A @ C @ B )
              <=> ( r1_tarski @ ( k1_yellow19 @ A @ B ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
               => ( ( r2_waybel_7 @ A @ C @ B )
                <=> ( r1_tarski @ ( k1_yellow19 @ A @ B ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_yellow19])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 )
    | ~ ( r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 )
   <= ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 )
    | ~ ( r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r2_waybel_7 @ A @ B @ C )
        <=> ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ D @ A )
                  & ( r2_hidden @ C @ D ) )
               => ( r2_hidden @ D @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ ( sk_D_1 @ X20 @ X21 @ X22 ) )
      | ( r2_waybel_7 @ X22 @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v3_pre_topc @ ( sk_D_1 @ X20 @ X21 @ X22 ) @ X22 )
      | ( r2_waybel_7 @ X22 @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ X20 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r2_waybel_7 @ X22 @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( m1_connsp_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( m1_connsp_2 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X0 @ X3 )
      | ~ ( r2_hidden @ X3 @ ( sk_D_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v3_pre_topc @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v3_pre_topc @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ X3 @ ( sk_D_1 @ X2 @ X1 @ X0 ) )
      | ( m1_connsp_2 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( m1_connsp_2 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X0 @ X3 )
      | ~ ( r2_hidden @ X3 @ ( sk_D_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( sk_D_1 @ X2 @ X1 @ X0 ) )
      | ( m1_connsp_2 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X0 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( m1_connsp_2 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_connsp_2 @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ( r2_waybel_7 @ X0 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_waybel_7 @ sk_A @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_7 @ sk_A @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_connsp_2 @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ sk_A @ sk_B )
      | ( r2_waybel_7 @ sk_A @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r2_hidden @ C @ ( k1_yellow19 @ A @ B ) )
            <=> ( m1_connsp_2 @ C @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X29: $i,X30: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_connsp_2 @ X32 @ X30 @ X29 )
      | ( r2_hidden @ X32 @ ( k1_yellow19 @ X30 @ X29 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow19])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_waybel_7 @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,
    ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 )
    | ( r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 )
   <= ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['29'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_2 )
        | ~ ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( r2_waybel_7 @ sk_A @ X0 @ sk_B )
        | ( r2_hidden @ ( sk_D_1 @ sk_B @ X0 @ sk_A ) @ sk_C_2 ) )
   <= ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ X20 @ X21 @ X22 ) @ X21 )
      | ( r2_waybel_7 @ X22 @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('35',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B ) )
   <= ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B )
      | ( r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B ) )
   <= ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B )
   <= ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B )
   <= ~ ( r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B )
    | ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','41'])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['1','42'])).

thf('44',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B )
   <= ( r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B ) ),
    inference(split,[status(esa)],['29'])).

thf('45',plain,
    ( ( r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B )
    | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['29'])).

thf('46',plain,(
    r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','41','45'])).

thf('47',plain,(
    r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B ),
    inference(simpl_trail,[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r2_hidden @ X31 @ ( k1_yellow19 @ X30 @ X29 ) )
      | ( m1_connsp_2 @ X31 @ X30 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow19])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) )
      | ( m1_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_connsp_2 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_connsp_2 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('60',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_connsp_2 @ X11 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf(t8_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ B @ D )
                    & ( r1_tarski @ D @ C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ( r2_hidden @ X15 @ ( sk_D @ X17 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ X1 @ sk_A ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ X1 @ sk_A ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_connsp_2 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('81',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ( v3_pre_topc @ ( sk_D @ X17 @ X15 @ X16 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ X1 @ sk_A ) @ sk_A )
      | ~ ( m1_connsp_2 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ X1 @ sk_A ) @ sk_A )
      | ~ ( m1_connsp_2 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_connsp_2 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('94',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ( m1_subset_1 @ ( sk_D @ X17 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ X1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ X1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_waybel_7 @ X22 @ X21 @ X23 )
      | ~ ( v3_pre_topc @ X24 @ X22 )
      | ~ ( r2_hidden @ X23 @ X24 )
      | ( r2_hidden @ X24 @ X21 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X2 @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_waybel_7 @ sk_A @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ X2 @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_waybel_7 @ sk_A @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_waybel_7 @ sk_A @ X2 @ X1 )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ X2 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ X2 )
      | ~ ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
      | ~ ( r2_waybel_7 @ sk_A @ X2 @ X1 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_waybel_7 @ sk_A @ X1 @ sk_B )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ X1 )
      | ~ ( r2_waybel_7 @ sk_A @ X1 @ sk_B )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['47','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_connsp_2 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('117',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ( r1_tarski @ ( sk_D @ X17 @ X15 @ X16 ) @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ X1 @ sk_A ) @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ X1 @ sk_A ) @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('129',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('131',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('132',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('133',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('134',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['131','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('137',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('138',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['135','138'])).

thf(t11_waybel_7,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) )
     => ( ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ D @ A )
              & ( r2_hidden @ C @ B ) )
           => ( r2_hidden @ D @ B ) ) ) ) )).

thf('140',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( v13_waybel_0 @ X25 @ ( k3_yellow_1 @ X26 ) )
      | ~ ( r2_hidden @ X27 @ X25 )
      | ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X26 )
      | ( r2_hidden @ X28 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X26 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t11_waybel_7])).

thf('141',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('142',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('143',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( v13_waybel_0 @ X25 @ ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) )
      | ~ ( r2_hidden @ X27 @ X25 )
      | ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X26 )
      | ( r2_hidden @ X28 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X26 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( v13_waybel_0 @ sk_C_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['139','143'])).

thf('145',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('146',plain,(
    v13_waybel_0 @ sk_C_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X19: $i] :
      ( ( k3_yellow_1 @ X19 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('148',plain,(
    v13_waybel_0 @ sk_C_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( v13_waybel_0 @ sk_C_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['145','148'])).

thf('150',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['136','137'])).

thf('151',plain,(
    v13_waybel_0 @ sk_C_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['144','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( r1_tarski @ X1 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['130','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 )
      | ~ ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_C_2 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_C_2 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['114','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('159',plain,
    ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 )
    | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    $false ),
    inference(demod,[status(thm)],['43','160'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LNlbpmUOQL
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:04:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 5.26/5.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.26/5.51  % Solved by: fo/fo7.sh
% 5.26/5.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.26/5.51  % done 1901 iterations in 5.045s
% 5.26/5.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.26/5.51  % SZS output start Refutation
% 5.26/5.51  thf(sk_C_2_type, type, sk_C_2: $i).
% 5.26/5.51  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 5.26/5.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.26/5.51  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 5.26/5.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.26/5.51  thf(sk_B_type, type, sk_B: $i).
% 5.26/5.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.26/5.51  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 5.26/5.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.26/5.51  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 5.26/5.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 5.26/5.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.26/5.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 5.26/5.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.26/5.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.26/5.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.26/5.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.26/5.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 5.26/5.51  thf(sk_A_type, type, sk_A: $i).
% 5.26/5.51  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 5.26/5.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.26/5.51  thf(k1_yellow19_type, type, k1_yellow19: $i > $i > $i).
% 5.26/5.51  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 5.26/5.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.26/5.51  thf(t4_yellow19, conjecture,
% 5.26/5.51    (![A:$i]:
% 5.26/5.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.26/5.51       ( ![B:$i]:
% 5.26/5.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.26/5.51           ( ![C:$i]:
% 5.26/5.51             ( ( ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 5.26/5.51                 ( m1_subset_1 @
% 5.26/5.51                   C @ 
% 5.26/5.51                   ( k1_zfmisc_1 @
% 5.26/5.51                     ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 5.26/5.51               ( ( r2_waybel_7 @ A @ C @ B ) <=>
% 5.26/5.51                 ( r1_tarski @ ( k1_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 5.26/5.51  thf(zf_stmt_0, negated_conjecture,
% 5.26/5.51    (~( ![A:$i]:
% 5.26/5.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 5.26/5.51            ( l1_pre_topc @ A ) ) =>
% 5.26/5.51          ( ![B:$i]:
% 5.26/5.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.26/5.51              ( ![C:$i]:
% 5.26/5.51                ( ( ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 5.26/5.51                    ( m1_subset_1 @
% 5.26/5.51                      C @ 
% 5.26/5.51                      ( k1_zfmisc_1 @
% 5.26/5.51                        ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 5.26/5.51                  ( ( r2_waybel_7 @ A @ C @ B ) <=>
% 5.26/5.51                    ( r1_tarski @ ( k1_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 5.26/5.51    inference('cnf.neg', [status(esa)], [t4_yellow19])).
% 5.26/5.51  thf('0', plain,
% 5.26/5.51      ((~ (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)
% 5.26/5.51        | ~ (r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B))),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('1', plain,
% 5.26/5.51      ((~ (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2))
% 5.26/5.51         <= (~ ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)))),
% 5.26/5.51      inference('split', [status(esa)], ['0'])).
% 5.26/5.51  thf('2', plain,
% 5.26/5.51      (~ ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)) | 
% 5.26/5.51       ~ ((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B))),
% 5.26/5.51      inference('split', [status(esa)], ['0'])).
% 5.26/5.51  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf(d5_waybel_7, axiom,
% 5.26/5.51    (![A:$i]:
% 5.26/5.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.26/5.51       ( ![B:$i,C:$i]:
% 5.26/5.51         ( ( r2_waybel_7 @ A @ B @ C ) <=>
% 5.26/5.51           ( ![D:$i]:
% 5.26/5.51             ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.26/5.51               ( ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) ) =>
% 5.26/5.51                 ( r2_hidden @ D @ B ) ) ) ) ) ) ))).
% 5.26/5.51  thf('4', plain,
% 5.26/5.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.26/5.51         ((r2_hidden @ X20 @ (sk_D_1 @ X20 @ X21 @ X22))
% 5.26/5.51          | (r2_waybel_7 @ X22 @ X21 @ X20)
% 5.26/5.51          | ~ (l1_pre_topc @ X22)
% 5.26/5.51          | ~ (v2_pre_topc @ X22))),
% 5.26/5.51      inference('cnf', [status(esa)], [d5_waybel_7])).
% 5.26/5.51  thf('5', plain,
% 5.26/5.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.26/5.51         ((v3_pre_topc @ (sk_D_1 @ X20 @ X21 @ X22) @ X22)
% 5.26/5.51          | (r2_waybel_7 @ X22 @ X21 @ X20)
% 5.26/5.51          | ~ (l1_pre_topc @ X22)
% 5.26/5.51          | ~ (v2_pre_topc @ X22))),
% 5.26/5.51      inference('cnf', [status(esa)], [d5_waybel_7])).
% 5.26/5.51  thf('6', plain,
% 5.26/5.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.26/5.51         ((m1_subset_1 @ (sk_D_1 @ X20 @ X21 @ X22) @ 
% 5.26/5.51           (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 5.26/5.51          | (r2_waybel_7 @ X22 @ X21 @ X20)
% 5.26/5.51          | ~ (l1_pre_topc @ X22)
% 5.26/5.51          | ~ (v2_pre_topc @ X22))),
% 5.26/5.51      inference('cnf', [status(esa)], [d5_waybel_7])).
% 5.26/5.51  thf(t5_connsp_2, axiom,
% 5.26/5.51    (![A:$i]:
% 5.26/5.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.26/5.51       ( ![B:$i]:
% 5.26/5.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.26/5.51           ( ![C:$i]:
% 5.26/5.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 5.26/5.51               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 5.26/5.51                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 5.26/5.51  thf('7', plain,
% 5.26/5.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 5.26/5.51         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 5.26/5.51          | ~ (v3_pre_topc @ X12 @ X13)
% 5.26/5.51          | ~ (r2_hidden @ X14 @ X12)
% 5.26/5.51          | (m1_connsp_2 @ X12 @ X13 @ X14)
% 5.26/5.51          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 5.26/5.51          | ~ (l1_pre_topc @ X13)
% 5.26/5.51          | ~ (v2_pre_topc @ X13)
% 5.26/5.51          | (v2_struct_0 @ X13))),
% 5.26/5.51      inference('cnf', [status(esa)], [t5_connsp_2])).
% 5.26/5.51  thf('8', plain,
% 5.26/5.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.26/5.51         (~ (v2_pre_topc @ X0)
% 5.26/5.51          | ~ (l1_pre_topc @ X0)
% 5.26/5.51          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 5.26/5.51          | (v2_struct_0 @ X0)
% 5.26/5.51          | ~ (v2_pre_topc @ X0)
% 5.26/5.51          | ~ (l1_pre_topc @ X0)
% 5.26/5.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 5.26/5.51          | (m1_connsp_2 @ (sk_D_1 @ X2 @ X1 @ X0) @ X0 @ X3)
% 5.26/5.51          | ~ (r2_hidden @ X3 @ (sk_D_1 @ X2 @ X1 @ X0))
% 5.26/5.51          | ~ (v3_pre_topc @ (sk_D_1 @ X2 @ X1 @ X0) @ X0))),
% 5.26/5.51      inference('sup-', [status(thm)], ['6', '7'])).
% 5.26/5.51  thf('9', plain,
% 5.26/5.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.26/5.51         (~ (v3_pre_topc @ (sk_D_1 @ X2 @ X1 @ X0) @ X0)
% 5.26/5.51          | ~ (r2_hidden @ X3 @ (sk_D_1 @ X2 @ X1 @ X0))
% 5.26/5.51          | (m1_connsp_2 @ (sk_D_1 @ X2 @ X1 @ X0) @ X0 @ X3)
% 5.26/5.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 5.26/5.51          | (v2_struct_0 @ X0)
% 5.26/5.51          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 5.26/5.51          | ~ (l1_pre_topc @ X0)
% 5.26/5.51          | ~ (v2_pre_topc @ X0))),
% 5.26/5.51      inference('simplify', [status(thm)], ['8'])).
% 5.26/5.51  thf('10', plain,
% 5.26/5.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.26/5.51         (~ (v2_pre_topc @ X0)
% 5.26/5.51          | ~ (l1_pre_topc @ X0)
% 5.26/5.51          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 5.26/5.51          | ~ (v2_pre_topc @ X0)
% 5.26/5.51          | ~ (l1_pre_topc @ X0)
% 5.26/5.51          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 5.26/5.51          | (v2_struct_0 @ X0)
% 5.26/5.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 5.26/5.51          | (m1_connsp_2 @ (sk_D_1 @ X2 @ X1 @ X0) @ X0 @ X3)
% 5.26/5.51          | ~ (r2_hidden @ X3 @ (sk_D_1 @ X2 @ X1 @ X0)))),
% 5.26/5.51      inference('sup-', [status(thm)], ['5', '9'])).
% 5.26/5.51  thf('11', plain,
% 5.26/5.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.26/5.51         (~ (r2_hidden @ X3 @ (sk_D_1 @ X2 @ X1 @ X0))
% 5.26/5.51          | (m1_connsp_2 @ (sk_D_1 @ X2 @ X1 @ X0) @ X0 @ X3)
% 5.26/5.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 5.26/5.51          | (v2_struct_0 @ X0)
% 5.26/5.51          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 5.26/5.51          | ~ (l1_pre_topc @ X0)
% 5.26/5.51          | ~ (v2_pre_topc @ X0))),
% 5.26/5.51      inference('simplify', [status(thm)], ['10'])).
% 5.26/5.51  thf('12', plain,
% 5.26/5.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.26/5.51         (~ (v2_pre_topc @ X0)
% 5.26/5.51          | ~ (l1_pre_topc @ X0)
% 5.26/5.51          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 5.26/5.51          | ~ (v2_pre_topc @ X0)
% 5.26/5.51          | ~ (l1_pre_topc @ X0)
% 5.26/5.51          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 5.26/5.51          | (v2_struct_0 @ X0)
% 5.26/5.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 5.26/5.51          | (m1_connsp_2 @ (sk_D_1 @ X2 @ X1 @ X0) @ X0 @ X2))),
% 5.26/5.51      inference('sup-', [status(thm)], ['4', '11'])).
% 5.26/5.51  thf('13', plain,
% 5.26/5.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.26/5.51         ((m1_connsp_2 @ (sk_D_1 @ X2 @ X1 @ X0) @ X0 @ X2)
% 5.26/5.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 5.26/5.51          | (v2_struct_0 @ X0)
% 5.26/5.51          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 5.26/5.51          | ~ (l1_pre_topc @ X0)
% 5.26/5.51          | ~ (v2_pre_topc @ X0))),
% 5.26/5.51      inference('simplify', [status(thm)], ['12'])).
% 5.26/5.51  thf('14', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         (~ (v2_pre_topc @ sk_A)
% 5.26/5.51          | ~ (l1_pre_topc @ sk_A)
% 5.26/5.51          | (r2_waybel_7 @ sk_A @ X0 @ sk_B)
% 5.26/5.51          | (v2_struct_0 @ sk_A)
% 5.26/5.51          | (m1_connsp_2 @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ sk_A @ sk_B))),
% 5.26/5.51      inference('sup-', [status(thm)], ['3', '13'])).
% 5.26/5.51  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('17', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((r2_waybel_7 @ sk_A @ X0 @ sk_B)
% 5.26/5.51          | (v2_struct_0 @ sk_A)
% 5.26/5.51          | (m1_connsp_2 @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ sk_A @ sk_B))),
% 5.26/5.51      inference('demod', [status(thm)], ['14', '15', '16'])).
% 5.26/5.51  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('19', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((m1_connsp_2 @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ sk_A @ sk_B)
% 5.26/5.51          | (r2_waybel_7 @ sk_A @ X0 @ sk_B))),
% 5.26/5.51      inference('clc', [status(thm)], ['17', '18'])).
% 5.26/5.51  thf('20', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf(t3_yellow19, axiom,
% 5.26/5.51    (![A:$i]:
% 5.26/5.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.26/5.51       ( ![B:$i]:
% 5.26/5.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.26/5.51           ( ![C:$i]:
% 5.26/5.51             ( ( r2_hidden @ C @ ( k1_yellow19 @ A @ B ) ) <=>
% 5.26/5.51               ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ))).
% 5.26/5.51  thf('21', plain,
% 5.26/5.51      (![X29 : $i, X30 : $i, X32 : $i]:
% 5.26/5.51         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 5.26/5.51          | ~ (m1_connsp_2 @ X32 @ X30 @ X29)
% 5.26/5.51          | (r2_hidden @ X32 @ (k1_yellow19 @ X30 @ X29))
% 5.26/5.51          | ~ (l1_pre_topc @ X30)
% 5.26/5.51          | ~ (v2_pre_topc @ X30)
% 5.26/5.51          | (v2_struct_0 @ X30))),
% 5.26/5.51      inference('cnf', [status(esa)], [t3_yellow19])).
% 5.26/5.51  thf('22', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((v2_struct_0 @ sk_A)
% 5.26/5.51          | ~ (v2_pre_topc @ sk_A)
% 5.26/5.51          | ~ (l1_pre_topc @ sk_A)
% 5.26/5.51          | (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B))
% 5.26/5.51          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 5.26/5.51      inference('sup-', [status(thm)], ['20', '21'])).
% 5.26/5.51  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('25', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((v2_struct_0 @ sk_A)
% 5.26/5.51          | (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B))
% 5.26/5.51          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 5.26/5.51      inference('demod', [status(thm)], ['22', '23', '24'])).
% 5.26/5.51  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('27', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 5.26/5.51          | (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))),
% 5.26/5.51      inference('clc', [status(thm)], ['25', '26'])).
% 5.26/5.51  thf('28', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((r2_waybel_7 @ sk_A @ X0 @ sk_B)
% 5.26/5.51          | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ 
% 5.26/5.51             (k1_yellow19 @ sk_A @ sk_B)))),
% 5.26/5.51      inference('sup-', [status(thm)], ['19', '27'])).
% 5.26/5.51  thf('29', plain,
% 5.26/5.51      (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)
% 5.26/5.51        | (r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B))),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('30', plain,
% 5.26/5.51      (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2))
% 5.26/5.51         <= (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)))),
% 5.26/5.51      inference('split', [status(esa)], ['29'])).
% 5.26/5.51  thf(d3_tarski, axiom,
% 5.26/5.51    (![A:$i,B:$i]:
% 5.26/5.51     ( ( r1_tarski @ A @ B ) <=>
% 5.26/5.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.26/5.51  thf('31', plain,
% 5.26/5.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.26/5.51         (~ (r2_hidden @ X0 @ X1)
% 5.26/5.51          | (r2_hidden @ X0 @ X2)
% 5.26/5.51          | ~ (r1_tarski @ X1 @ X2))),
% 5.26/5.51      inference('cnf', [status(esa)], [d3_tarski])).
% 5.26/5.51  thf('32', plain,
% 5.26/5.51      ((![X0 : $i]:
% 5.26/5.51          ((r2_hidden @ X0 @ sk_C_2)
% 5.26/5.51           | ~ (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B))))
% 5.26/5.51         <= (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)))),
% 5.26/5.51      inference('sup-', [status(thm)], ['30', '31'])).
% 5.26/5.51  thf('33', plain,
% 5.26/5.51      ((![X0 : $i]:
% 5.26/5.51          ((r2_waybel_7 @ sk_A @ X0 @ sk_B)
% 5.26/5.51           | (r2_hidden @ (sk_D_1 @ sk_B @ X0 @ sk_A) @ sk_C_2)))
% 5.26/5.51         <= (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)))),
% 5.26/5.51      inference('sup-', [status(thm)], ['28', '32'])).
% 5.26/5.51  thf('34', plain,
% 5.26/5.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.26/5.51         (~ (r2_hidden @ (sk_D_1 @ X20 @ X21 @ X22) @ X21)
% 5.26/5.51          | (r2_waybel_7 @ X22 @ X21 @ X20)
% 5.26/5.51          | ~ (l1_pre_topc @ X22)
% 5.26/5.51          | ~ (v2_pre_topc @ X22))),
% 5.26/5.51      inference('cnf', [status(esa)], [d5_waybel_7])).
% 5.26/5.51  thf('35', plain,
% 5.26/5.51      ((((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)
% 5.26/5.51         | ~ (v2_pre_topc @ sk_A)
% 5.26/5.51         | ~ (l1_pre_topc @ sk_A)
% 5.26/5.51         | (r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)))
% 5.26/5.51         <= (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)))),
% 5.26/5.51      inference('sup-', [status(thm)], ['33', '34'])).
% 5.26/5.51  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('38', plain,
% 5.26/5.51      ((((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)
% 5.26/5.51         | (r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)))
% 5.26/5.51         <= (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)))),
% 5.26/5.51      inference('demod', [status(thm)], ['35', '36', '37'])).
% 5.26/5.51  thf('39', plain,
% 5.26/5.51      (((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B))
% 5.26/5.51         <= (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)))),
% 5.26/5.51      inference('simplify', [status(thm)], ['38'])).
% 5.26/5.51  thf('40', plain,
% 5.26/5.51      ((~ (r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B))
% 5.26/5.51         <= (~ ((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)))),
% 5.26/5.51      inference('split', [status(esa)], ['0'])).
% 5.26/5.51  thf('41', plain,
% 5.26/5.51      (((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)) | 
% 5.26/5.51       ~ ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2))),
% 5.26/5.51      inference('sup-', [status(thm)], ['39', '40'])).
% 5.26/5.51  thf('42', plain, (~ ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2))),
% 5.26/5.51      inference('sat_resolution*', [status(thm)], ['2', '41'])).
% 5.26/5.51  thf('43', plain, (~ (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)),
% 5.26/5.51      inference('simpl_trail', [status(thm)], ['1', '42'])).
% 5.26/5.51  thf('44', plain,
% 5.26/5.51      (((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B))
% 5.26/5.51         <= (((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)))),
% 5.26/5.51      inference('split', [status(esa)], ['29'])).
% 5.26/5.51  thf('45', plain,
% 5.26/5.51      (((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)) | 
% 5.26/5.51       ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2))),
% 5.26/5.51      inference('split', [status(esa)], ['29'])).
% 5.26/5.51  thf('46', plain, (((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B))),
% 5.26/5.51      inference('sat_resolution*', [status(thm)], ['2', '41', '45'])).
% 5.26/5.51  thf('47', plain, ((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)),
% 5.26/5.51      inference('simpl_trail', [status(thm)], ['44', '46'])).
% 5.26/5.51  thf('48', plain,
% 5.26/5.51      (![X1 : $i, X3 : $i]:
% 5.26/5.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.26/5.51      inference('cnf', [status(esa)], [d3_tarski])).
% 5.26/5.51  thf('49', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('50', plain,
% 5.26/5.51      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.26/5.51         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 5.26/5.51          | ~ (r2_hidden @ X31 @ (k1_yellow19 @ X30 @ X29))
% 5.26/5.51          | (m1_connsp_2 @ X31 @ X30 @ X29)
% 5.26/5.51          | ~ (l1_pre_topc @ X30)
% 5.26/5.51          | ~ (v2_pre_topc @ X30)
% 5.26/5.51          | (v2_struct_0 @ X30))),
% 5.26/5.51      inference('cnf', [status(esa)], [t3_yellow19])).
% 5.26/5.51  thf('51', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((v2_struct_0 @ sk_A)
% 5.26/5.51          | ~ (v2_pre_topc @ sk_A)
% 5.26/5.51          | ~ (l1_pre_topc @ sk_A)
% 5.26/5.51          | (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 5.26/5.51          | ~ (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))),
% 5.26/5.51      inference('sup-', [status(thm)], ['49', '50'])).
% 5.26/5.51  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('54', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((v2_struct_0 @ sk_A)
% 5.26/5.51          | (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 5.26/5.51          | ~ (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))),
% 5.26/5.51      inference('demod', [status(thm)], ['51', '52', '53'])).
% 5.26/5.51  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('56', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         (~ (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B))
% 5.26/5.51          | (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 5.26/5.51      inference('clc', [status(thm)], ['54', '55'])).
% 5.26/5.51  thf('57', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.51          | (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_A @ 
% 5.26/5.51             sk_B))),
% 5.26/5.51      inference('sup-', [status(thm)], ['48', '56'])).
% 5.26/5.51  thf('58', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.51          | (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_A @ 
% 5.26/5.51             sk_B))),
% 5.26/5.51      inference('sup-', [status(thm)], ['48', '56'])).
% 5.26/5.51  thf('59', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf(dt_m1_connsp_2, axiom,
% 5.26/5.51    (![A:$i,B:$i]:
% 5.26/5.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 5.26/5.51         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 5.26/5.51       ( ![C:$i]:
% 5.26/5.51         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 5.26/5.51           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 5.26/5.51  thf('60', plain,
% 5.26/5.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.26/5.51         (~ (l1_pre_topc @ X9)
% 5.26/5.51          | ~ (v2_pre_topc @ X9)
% 5.26/5.51          | (v2_struct_0 @ X9)
% 5.26/5.51          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 5.26/5.51          | (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 5.26/5.51          | ~ (m1_connsp_2 @ X11 @ X9 @ X10))),
% 5.26/5.51      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 5.26/5.51  thf('61', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 5.26/5.51          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.26/5.51          | (v2_struct_0 @ sk_A)
% 5.26/5.51          | ~ (v2_pre_topc @ sk_A)
% 5.26/5.51          | ~ (l1_pre_topc @ sk_A))),
% 5.26/5.51      inference('sup-', [status(thm)], ['59', '60'])).
% 5.26/5.51  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('64', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 5.26/5.51          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.26/5.51          | (v2_struct_0 @ sk_A))),
% 5.26/5.51      inference('demod', [status(thm)], ['61', '62', '63'])).
% 5.26/5.51  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('66', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.26/5.51          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 5.26/5.51      inference('clc', [status(thm)], ['64', '65'])).
% 5.26/5.51  thf('67', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.51          | (m1_subset_1 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 5.26/5.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.26/5.51      inference('sup-', [status(thm)], ['58', '66'])).
% 5.26/5.51  thf(t8_connsp_2, axiom,
% 5.26/5.51    (![A:$i]:
% 5.26/5.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.26/5.51       ( ![B:$i]:
% 5.26/5.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.26/5.51           ( ![C:$i]:
% 5.26/5.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.26/5.51               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 5.26/5.51                 ( ?[D:$i]:
% 5.26/5.51                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 5.26/5.51                     ( v3_pre_topc @ D @ A ) & 
% 5.26/5.51                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 5.26/5.51  thf('68', plain,
% 5.26/5.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.26/5.51         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 5.26/5.51          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 5.26/5.51          | (r2_hidden @ X15 @ (sk_D @ X17 @ X15 @ X16))
% 5.26/5.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 5.26/5.51          | ~ (l1_pre_topc @ X16)
% 5.26/5.51          | ~ (v2_pre_topc @ X16)
% 5.26/5.51          | (v2_struct_0 @ X16))),
% 5.26/5.51      inference('cnf', [status(esa)], [t8_connsp_2])).
% 5.26/5.51  thf('69', plain,
% 5.26/5.51      (![X0 : $i, X1 : $i]:
% 5.26/5.51         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.51          | (v2_struct_0 @ sk_A)
% 5.26/5.51          | ~ (v2_pre_topc @ sk_A)
% 5.26/5.51          | ~ (l1_pre_topc @ sk_A)
% 5.26/5.51          | (r2_hidden @ X1 @ 
% 5.26/5.51             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ X1 @ sk_A))
% 5.26/5.51          | ~ (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 5.26/5.51               sk_A @ X1)
% 5.26/5.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 5.26/5.51      inference('sup-', [status(thm)], ['67', '68'])).
% 5.26/5.51  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('72', plain,
% 5.26/5.51      (![X0 : $i, X1 : $i]:
% 5.26/5.51         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.51          | (v2_struct_0 @ sk_A)
% 5.26/5.51          | (r2_hidden @ X1 @ 
% 5.26/5.51             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ X1 @ sk_A))
% 5.26/5.51          | ~ (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 5.26/5.51               sk_A @ X1)
% 5.26/5.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 5.26/5.51      inference('demod', [status(thm)], ['69', '70', '71'])).
% 5.26/5.51  thf('73', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.51          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.26/5.51          | (r2_hidden @ sk_B @ 
% 5.26/5.51             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A))
% 5.26/5.51          | (v2_struct_0 @ sk_A)
% 5.26/5.51          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.51      inference('sup-', [status(thm)], ['57', '72'])).
% 5.26/5.51  thf('74', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('75', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.51          | (r2_hidden @ sk_B @ 
% 5.26/5.51             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A))
% 5.26/5.51          | (v2_struct_0 @ sk_A)
% 5.26/5.51          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.51      inference('demod', [status(thm)], ['73', '74'])).
% 5.26/5.51  thf('76', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((v2_struct_0 @ sk_A)
% 5.26/5.51          | (r2_hidden @ sk_B @ 
% 5.26/5.51             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A))
% 5.26/5.51          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.51      inference('simplify', [status(thm)], ['75'])).
% 5.26/5.51  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('78', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.51          | (r2_hidden @ sk_B @ 
% 5.26/5.51             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A)))),
% 5.26/5.51      inference('clc', [status(thm)], ['76', '77'])).
% 5.26/5.51  thf('79', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.51          | (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_A @ 
% 5.26/5.51             sk_B))),
% 5.26/5.51      inference('sup-', [status(thm)], ['48', '56'])).
% 5.26/5.51  thf('80', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.51          | (m1_subset_1 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 5.26/5.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.26/5.51      inference('sup-', [status(thm)], ['58', '66'])).
% 5.26/5.51  thf('81', plain,
% 5.26/5.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.26/5.51         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 5.26/5.51          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 5.26/5.51          | (v3_pre_topc @ (sk_D @ X17 @ X15 @ X16) @ X16)
% 5.26/5.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 5.26/5.51          | ~ (l1_pre_topc @ X16)
% 5.26/5.51          | ~ (v2_pre_topc @ X16)
% 5.26/5.51          | (v2_struct_0 @ X16))),
% 5.26/5.51      inference('cnf', [status(esa)], [t8_connsp_2])).
% 5.26/5.51  thf('82', plain,
% 5.26/5.51      (![X0 : $i, X1 : $i]:
% 5.26/5.51         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.51          | (v2_struct_0 @ sk_A)
% 5.26/5.51          | ~ (v2_pre_topc @ sk_A)
% 5.26/5.51          | ~ (l1_pre_topc @ sk_A)
% 5.26/5.51          | (v3_pre_topc @ 
% 5.26/5.51             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ X1 @ sk_A) @ 
% 5.26/5.51             sk_A)
% 5.26/5.51          | ~ (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 5.26/5.51               sk_A @ X1)
% 5.26/5.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 5.26/5.51      inference('sup-', [status(thm)], ['80', '81'])).
% 5.26/5.51  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('85', plain,
% 5.26/5.51      (![X0 : $i, X1 : $i]:
% 5.26/5.51         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.51          | (v2_struct_0 @ sk_A)
% 5.26/5.51          | (v3_pre_topc @ 
% 5.26/5.51             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ X1 @ sk_A) @ 
% 5.26/5.51             sk_A)
% 5.26/5.51          | ~ (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 5.26/5.51               sk_A @ X1)
% 5.26/5.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 5.26/5.51      inference('demod', [status(thm)], ['82', '83', '84'])).
% 5.26/5.51  thf('86', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.51          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.26/5.51          | (v3_pre_topc @ 
% 5.26/5.51             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.51             sk_A)
% 5.26/5.51          | (v2_struct_0 @ sk_A)
% 5.26/5.51          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.51      inference('sup-', [status(thm)], ['79', '85'])).
% 5.26/5.51  thf('87', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.26/5.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.51  thf('88', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.51         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.51          | (v3_pre_topc @ 
% 5.26/5.51             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.51             sk_A)
% 5.26/5.51          | (v2_struct_0 @ sk_A)
% 5.26/5.51          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.51      inference('demod', [status(thm)], ['86', '87'])).
% 5.26/5.51  thf('89', plain,
% 5.26/5.51      (![X0 : $i]:
% 5.26/5.52         ((v2_struct_0 @ sk_A)
% 5.26/5.52          | (v3_pre_topc @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             sk_A)
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.52      inference('simplify', [status(thm)], ['88'])).
% 5.26/5.52  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 5.26/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.52  thf('91', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (v3_pre_topc @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             sk_A))),
% 5.26/5.52      inference('clc', [status(thm)], ['89', '90'])).
% 5.26/5.52  thf('92', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_A @ 
% 5.26/5.52             sk_B))),
% 5.26/5.52      inference('sup-', [status(thm)], ['48', '56'])).
% 5.26/5.52  thf('93', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (m1_subset_1 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 5.26/5.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.26/5.52      inference('sup-', [status(thm)], ['58', '66'])).
% 5.26/5.52  thf('94', plain,
% 5.26/5.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.26/5.52         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 5.26/5.52          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 5.26/5.52          | (m1_subset_1 @ (sk_D @ X17 @ X15 @ X16) @ 
% 5.26/5.52             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 5.26/5.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 5.26/5.52          | ~ (l1_pre_topc @ X16)
% 5.26/5.52          | ~ (v2_pre_topc @ X16)
% 5.26/5.52          | (v2_struct_0 @ X16))),
% 5.26/5.52      inference('cnf', [status(esa)], [t8_connsp_2])).
% 5.26/5.52  thf('95', plain,
% 5.26/5.52      (![X0 : $i, X1 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (v2_struct_0 @ sk_A)
% 5.26/5.52          | ~ (v2_pre_topc @ sk_A)
% 5.26/5.52          | ~ (l1_pre_topc @ sk_A)
% 5.26/5.52          | (m1_subset_1 @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ X1 @ sk_A) @ 
% 5.26/5.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.26/5.52          | ~ (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 5.26/5.52               sk_A @ X1)
% 5.26/5.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 5.26/5.52      inference('sup-', [status(thm)], ['93', '94'])).
% 5.26/5.52  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 5.26/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.52  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 5.26/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.52  thf('98', plain,
% 5.26/5.52      (![X0 : $i, X1 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (v2_struct_0 @ sk_A)
% 5.26/5.52          | (m1_subset_1 @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ X1 @ sk_A) @ 
% 5.26/5.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.26/5.52          | ~ (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 5.26/5.52               sk_A @ X1)
% 5.26/5.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 5.26/5.52      inference('demod', [status(thm)], ['95', '96', '97'])).
% 5.26/5.52  thf('99', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.26/5.52          | (m1_subset_1 @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.26/5.52          | (v2_struct_0 @ sk_A)
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.52      inference('sup-', [status(thm)], ['92', '98'])).
% 5.26/5.52  thf('100', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.26/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.52  thf('101', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (m1_subset_1 @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.26/5.52          | (v2_struct_0 @ sk_A)
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.52      inference('demod', [status(thm)], ['99', '100'])).
% 5.26/5.52  thf('102', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((v2_struct_0 @ sk_A)
% 5.26/5.52          | (m1_subset_1 @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.52      inference('simplify', [status(thm)], ['101'])).
% 5.26/5.52  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 5.26/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.52  thf('104', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (m1_subset_1 @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.26/5.52      inference('clc', [status(thm)], ['102', '103'])).
% 5.26/5.52  thf('105', plain,
% 5.26/5.52      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 5.26/5.52         (~ (r2_waybel_7 @ X22 @ X21 @ X23)
% 5.26/5.52          | ~ (v3_pre_topc @ X24 @ X22)
% 5.26/5.52          | ~ (r2_hidden @ X23 @ X24)
% 5.26/5.52          | (r2_hidden @ X24 @ X21)
% 5.26/5.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 5.26/5.52          | ~ (l1_pre_topc @ X22)
% 5.26/5.52          | ~ (v2_pre_topc @ X22))),
% 5.26/5.52      inference('cnf', [status(esa)], [d5_waybel_7])).
% 5.26/5.52  thf('106', plain,
% 5.26/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | ~ (v2_pre_topc @ sk_A)
% 5.26/5.52          | ~ (l1_pre_topc @ sk_A)
% 5.26/5.52          | (r2_hidden @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             X1)
% 5.26/5.52          | ~ (r2_hidden @ X2 @ 
% 5.26/5.52               (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A))
% 5.26/5.52          | ~ (v3_pre_topc @ 
% 5.26/5.52               (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52               sk_A)
% 5.26/5.52          | ~ (r2_waybel_7 @ sk_A @ X1 @ X2))),
% 5.26/5.52      inference('sup-', [status(thm)], ['104', '105'])).
% 5.26/5.52  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 5.26/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.52  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 5.26/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.52  thf('109', plain,
% 5.26/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (r2_hidden @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             X1)
% 5.26/5.52          | ~ (r2_hidden @ X2 @ 
% 5.26/5.52               (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A))
% 5.26/5.52          | ~ (v3_pre_topc @ 
% 5.26/5.52               (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52               sk_A)
% 5.26/5.52          | ~ (r2_waybel_7 @ sk_A @ X1 @ X2))),
% 5.26/5.52      inference('demod', [status(thm)], ['106', '107', '108'])).
% 5.26/5.52  thf('110', plain,
% 5.26/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | ~ (r2_waybel_7 @ sk_A @ X2 @ X1)
% 5.26/5.52          | ~ (r2_hidden @ X1 @ 
% 5.26/5.52               (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A))
% 5.26/5.52          | (r2_hidden @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             X2)
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.52      inference('sup-', [status(thm)], ['91', '109'])).
% 5.26/5.52  thf('111', plain,
% 5.26/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.26/5.52         ((r2_hidden @ 
% 5.26/5.52           (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52           X2)
% 5.26/5.52          | ~ (r2_hidden @ X1 @ 
% 5.26/5.52               (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A))
% 5.26/5.52          | ~ (r2_waybel_7 @ sk_A @ X2 @ X1)
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.52      inference('simplify', [status(thm)], ['110'])).
% 5.26/5.52  thf('112', plain,
% 5.26/5.52      (![X0 : $i, X1 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | ~ (r2_waybel_7 @ sk_A @ X1 @ sk_B)
% 5.26/5.52          | (r2_hidden @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             X1))),
% 5.26/5.52      inference('sup-', [status(thm)], ['78', '111'])).
% 5.26/5.52  thf('113', plain,
% 5.26/5.52      (![X0 : $i, X1 : $i]:
% 5.26/5.52         ((r2_hidden @ 
% 5.26/5.52           (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52           X1)
% 5.26/5.52          | ~ (r2_waybel_7 @ sk_A @ X1 @ sk_B)
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.52      inference('simplify', [status(thm)], ['112'])).
% 5.26/5.52  thf('114', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (r2_hidden @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             sk_C_2))),
% 5.26/5.52      inference('sup-', [status(thm)], ['47', '113'])).
% 5.26/5.52  thf('115', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_A @ 
% 5.26/5.52             sk_B))),
% 5.26/5.52      inference('sup-', [status(thm)], ['48', '56'])).
% 5.26/5.52  thf('116', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (m1_subset_1 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 5.26/5.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.26/5.52      inference('sup-', [status(thm)], ['58', '66'])).
% 5.26/5.52  thf('117', plain,
% 5.26/5.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.26/5.52         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 5.26/5.52          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 5.26/5.52          | (r1_tarski @ (sk_D @ X17 @ X15 @ X16) @ X17)
% 5.26/5.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 5.26/5.52          | ~ (l1_pre_topc @ X16)
% 5.26/5.52          | ~ (v2_pre_topc @ X16)
% 5.26/5.52          | (v2_struct_0 @ X16))),
% 5.26/5.52      inference('cnf', [status(esa)], [t8_connsp_2])).
% 5.26/5.52  thf('118', plain,
% 5.26/5.52      (![X0 : $i, X1 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (v2_struct_0 @ sk_A)
% 5.26/5.52          | ~ (v2_pre_topc @ sk_A)
% 5.26/5.52          | ~ (l1_pre_topc @ sk_A)
% 5.26/5.52          | (r1_tarski @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ X1 @ sk_A) @ 
% 5.26/5.52             (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))
% 5.26/5.52          | ~ (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 5.26/5.52               sk_A @ X1)
% 5.26/5.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 5.26/5.52      inference('sup-', [status(thm)], ['116', '117'])).
% 5.26/5.52  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 5.26/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.52  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 5.26/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.52  thf('121', plain,
% 5.26/5.52      (![X0 : $i, X1 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (v2_struct_0 @ sk_A)
% 5.26/5.52          | (r1_tarski @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ X1 @ sk_A) @ 
% 5.26/5.52             (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))
% 5.26/5.52          | ~ (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 5.26/5.52               sk_A @ X1)
% 5.26/5.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 5.26/5.52      inference('demod', [status(thm)], ['118', '119', '120'])).
% 5.26/5.52  thf('122', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.26/5.52          | (r1_tarski @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))
% 5.26/5.52          | (v2_struct_0 @ sk_A)
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.52      inference('sup-', [status(thm)], ['115', '121'])).
% 5.26/5.52  thf('123', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 5.26/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.52  thf('124', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (r1_tarski @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))
% 5.26/5.52          | (v2_struct_0 @ sk_A)
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.52      inference('demod', [status(thm)], ['122', '123'])).
% 5.26/5.52  thf('125', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((v2_struct_0 @ sk_A)
% 5.26/5.52          | (r1_tarski @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.52      inference('simplify', [status(thm)], ['124'])).
% 5.26/5.52  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 5.26/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.52  thf('127', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (r1_tarski @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))))),
% 5.26/5.52      inference('clc', [status(thm)], ['125', '126'])).
% 5.26/5.52  thf('128', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (m1_subset_1 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 5.26/5.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.26/5.52      inference('sup-', [status(thm)], ['58', '66'])).
% 5.26/5.52  thf(t3_subset, axiom,
% 5.26/5.52    (![A:$i,B:$i]:
% 5.26/5.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.26/5.52  thf('129', plain,
% 5.26/5.52      (![X4 : $i, X5 : $i]:
% 5.26/5.52         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 5.26/5.52      inference('cnf', [status(esa)], [t3_subset])).
% 5.26/5.52  thf('130', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (r1_tarski @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 5.26/5.52             (u1_struct_0 @ sk_A)))),
% 5.26/5.52      inference('sup-', [status(thm)], ['128', '129'])).
% 5.26/5.52  thf(d3_struct_0, axiom,
% 5.26/5.52    (![A:$i]:
% 5.26/5.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 5.26/5.52  thf('131', plain,
% 5.26/5.52      (![X7 : $i]:
% 5.26/5.52         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 5.26/5.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.26/5.52  thf('132', plain,
% 5.26/5.52      ((m1_subset_1 @ sk_C_2 @ 
% 5.26/5.52        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 5.26/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.52  thf(d2_yellow_1, axiom,
% 5.26/5.52    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 5.26/5.52  thf('133', plain,
% 5.26/5.52      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 5.26/5.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 5.26/5.52  thf('134', plain,
% 5.26/5.52      ((m1_subset_1 @ sk_C_2 @ 
% 5.26/5.52        (k1_zfmisc_1 @ 
% 5.26/5.52         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 5.26/5.52      inference('demod', [status(thm)], ['132', '133'])).
% 5.26/5.52  thf('135', plain,
% 5.26/5.52      (((m1_subset_1 @ sk_C_2 @ 
% 5.26/5.52         (k1_zfmisc_1 @ 
% 5.26/5.52          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 5.26/5.52        | ~ (l1_struct_0 @ sk_A))),
% 5.26/5.52      inference('sup+', [status(thm)], ['131', '134'])).
% 5.26/5.52  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 5.26/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.52  thf(dt_l1_pre_topc, axiom,
% 5.26/5.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 5.26/5.52  thf('137', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 5.26/5.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 5.26/5.52  thf('138', plain, ((l1_struct_0 @ sk_A)),
% 5.26/5.52      inference('sup-', [status(thm)], ['136', '137'])).
% 5.26/5.52  thf('139', plain,
% 5.26/5.52      ((m1_subset_1 @ sk_C_2 @ 
% 5.26/5.52        (k1_zfmisc_1 @ 
% 5.26/5.52         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 5.26/5.52      inference('demod', [status(thm)], ['135', '138'])).
% 5.26/5.52  thf(t11_waybel_7, axiom,
% 5.26/5.52    (![A:$i,B:$i]:
% 5.26/5.52     ( ( m1_subset_1 @
% 5.26/5.52         B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) =>
% 5.26/5.52       ( ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) <=>
% 5.26/5.52         ( ![C:$i,D:$i]:
% 5.26/5.52           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ D @ A ) & 
% 5.26/5.52               ( r2_hidden @ C @ B ) ) =>
% 5.26/5.52             ( r2_hidden @ D @ B ) ) ) ) ))).
% 5.26/5.52  thf('140', plain,
% 5.26/5.52      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 5.26/5.52         (~ (v13_waybel_0 @ X25 @ (k3_yellow_1 @ X26))
% 5.26/5.52          | ~ (r2_hidden @ X27 @ X25)
% 5.26/5.52          | ~ (r1_tarski @ X27 @ X28)
% 5.26/5.52          | ~ (r1_tarski @ X28 @ X26)
% 5.26/5.52          | (r2_hidden @ X28 @ X25)
% 5.26/5.52          | ~ (m1_subset_1 @ X25 @ 
% 5.26/5.52               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X26)))))),
% 5.26/5.52      inference('cnf', [status(esa)], [t11_waybel_7])).
% 5.26/5.52  thf('141', plain,
% 5.26/5.52      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 5.26/5.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 5.26/5.52  thf('142', plain,
% 5.26/5.52      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 5.26/5.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 5.26/5.52  thf('143', plain,
% 5.26/5.52      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 5.26/5.52         (~ (v13_waybel_0 @ X25 @ (k3_lattice3 @ (k1_lattice3 @ X26)))
% 5.26/5.52          | ~ (r2_hidden @ X27 @ X25)
% 5.26/5.52          | ~ (r1_tarski @ X27 @ X28)
% 5.26/5.52          | ~ (r1_tarski @ X28 @ X26)
% 5.26/5.52          | (r2_hidden @ X28 @ X25)
% 5.26/5.52          | ~ (m1_subset_1 @ X25 @ 
% 5.26/5.52               (k1_zfmisc_1 @ 
% 5.26/5.52                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X26))))))),
% 5.26/5.52      inference('demod', [status(thm)], ['140', '141', '142'])).
% 5.26/5.52  thf('144', plain,
% 5.26/5.52      (![X0 : $i, X1 : $i]:
% 5.26/5.52         ((r2_hidden @ X0 @ sk_C_2)
% 5.26/5.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A))
% 5.26/5.52          | ~ (r1_tarski @ X1 @ X0)
% 5.26/5.52          | ~ (r2_hidden @ X1 @ sk_C_2)
% 5.26/5.52          | ~ (v13_waybel_0 @ sk_C_2 @ 
% 5.26/5.52               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 5.26/5.52      inference('sup-', [status(thm)], ['139', '143'])).
% 5.26/5.52  thf('145', plain,
% 5.26/5.52      (![X7 : $i]:
% 5.26/5.52         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 5.26/5.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.26/5.52  thf('146', plain,
% 5.26/5.52      ((v13_waybel_0 @ sk_C_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 5.26/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.26/5.52  thf('147', plain,
% 5.26/5.52      (![X19 : $i]: ((k3_yellow_1 @ X19) = (k3_lattice3 @ (k1_lattice3 @ X19)))),
% 5.26/5.52      inference('cnf', [status(esa)], [d2_yellow_1])).
% 5.26/5.52  thf('148', plain,
% 5.26/5.52      ((v13_waybel_0 @ sk_C_2 @ 
% 5.26/5.52        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 5.26/5.52      inference('demod', [status(thm)], ['146', '147'])).
% 5.26/5.52  thf('149', plain,
% 5.26/5.52      (((v13_waybel_0 @ sk_C_2 @ 
% 5.26/5.52         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 5.26/5.52        | ~ (l1_struct_0 @ sk_A))),
% 5.26/5.52      inference('sup+', [status(thm)], ['145', '148'])).
% 5.26/5.52  thf('150', plain, ((l1_struct_0 @ sk_A)),
% 5.26/5.52      inference('sup-', [status(thm)], ['136', '137'])).
% 5.26/5.52  thf('151', plain,
% 5.26/5.52      ((v13_waybel_0 @ sk_C_2 @ 
% 5.26/5.52        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 5.26/5.52      inference('demod', [status(thm)], ['149', '150'])).
% 5.26/5.52  thf('152', plain,
% 5.26/5.52      (![X0 : $i, X1 : $i]:
% 5.26/5.52         ((r2_hidden @ X0 @ sk_C_2)
% 5.26/5.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A))
% 5.26/5.52          | ~ (r1_tarski @ X1 @ X0)
% 5.26/5.52          | ~ (r2_hidden @ X1 @ sk_C_2))),
% 5.26/5.52      inference('demod', [status(thm)], ['144', '151'])).
% 5.26/5.52  thf('153', plain,
% 5.26/5.52      (![X0 : $i, X1 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | ~ (r2_hidden @ X1 @ sk_C_2)
% 5.26/5.52          | ~ (r1_tarski @ X1 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))
% 5.26/5.52          | (r2_hidden @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_C_2))),
% 5.26/5.52      inference('sup-', [status(thm)], ['130', '152'])).
% 5.26/5.52  thf('154', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (r2_hidden @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_C_2)
% 5.26/5.52          | ~ (r2_hidden @ 
% 5.26/5.52               (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52               sk_C_2)
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.52      inference('sup-', [status(thm)], ['127', '153'])).
% 5.26/5.52  thf('155', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         (~ (r2_hidden @ 
% 5.26/5.52             (sk_D @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_B @ sk_A) @ 
% 5.26/5.52             sk_C_2)
% 5.26/5.52          | (r2_hidden @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_C_2)
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.52      inference('simplify', [status(thm)], ['154'])).
% 5.26/5.52  thf('156', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 5.26/5.52          | (r2_hidden @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_C_2))),
% 5.26/5.52      inference('sup-', [status(thm)], ['114', '155'])).
% 5.26/5.52  thf('157', plain,
% 5.26/5.52      (![X0 : $i]:
% 5.26/5.52         ((r2_hidden @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_C_2)
% 5.26/5.52          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 5.26/5.52      inference('simplify', [status(thm)], ['156'])).
% 5.26/5.52  thf('158', plain,
% 5.26/5.52      (![X1 : $i, X3 : $i]:
% 5.26/5.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.26/5.52      inference('cnf', [status(esa)], [d3_tarski])).
% 5.26/5.52  thf('159', plain,
% 5.26/5.52      (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)
% 5.26/5.52        | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2))),
% 5.26/5.52      inference('sup-', [status(thm)], ['157', '158'])).
% 5.26/5.52  thf('160', plain, ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)),
% 5.26/5.52      inference('simplify', [status(thm)], ['159'])).
% 5.26/5.52  thf('161', plain, ($false), inference('demod', [status(thm)], ['43', '160'])).
% 5.26/5.52  
% 5.26/5.52  % SZS output end Refutation
% 5.26/5.52  
% 5.26/5.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
