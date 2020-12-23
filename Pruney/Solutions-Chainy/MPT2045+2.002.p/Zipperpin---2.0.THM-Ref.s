%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PQSYGMKjSe

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:38 EST 2020

% Result     : Theorem 4.45s
% Output     : Refutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 513 expanded)
%              Number of leaves         :   39 ( 158 expanded)
%              Depth                    :   24
%              Number of atoms          : 1933 (9021 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_yellow19_type,type,(
    k1_yellow19: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X28 @ ( sk_D @ X28 @ X29 @ X30 ) )
      | ( r2_waybel_7 @ X30 @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v3_pre_topc @ ( sk_D @ X28 @ X29 @ X30 ) @ X30 )
      | ( r2_waybel_7 @ X30 @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X28 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r2_waybel_7 @ X30 @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X25 )
      | ~ ( r2_hidden @ X26 @ X24 )
      | ( m1_connsp_2 @ X24 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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
      | ( m1_connsp_2 @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 @ X3 )
      | ~ ( r2_hidden @ X3 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ~ ( v3_pre_topc @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v3_pre_topc @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ X3 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ( m1_connsp_2 @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 @ X3 )
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
      | ( m1_connsp_2 @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 @ X3 )
      | ~ ( r2_hidden @ X3 @ ( sk_D @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( sk_D @ X2 @ X1 @ X0 ) )
      | ( m1_connsp_2 @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 @ X3 )
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
      | ( m1_connsp_2 @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_connsp_2 @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 @ X2 )
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
      | ( m1_connsp_2 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A @ sk_B ) ) ),
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
      | ( m1_connsp_2 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_connsp_2 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A @ sk_B )
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
    ! [X37: $i,X38: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_connsp_2 @ X40 @ X38 @ X37 )
      | ( r2_hidden @ X40 @ ( k1_yellow19 @ X38 @ X37 ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
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
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ),
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
        | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_C_2 ) )
   <= ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X28 @ X29 @ X30 ) @ X29 )
      | ( r2_waybel_7 @ X30 @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ~ ( r2_hidden @ X39 @ ( k1_yellow19 @ X38 @ X37 ) )
      | ( m1_connsp_2 @ X39 @ X38 @ X37 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_connsp_2 @ X23 @ X21 @ X22 ) ) ),
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

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_connsp_2 @ X20 @ X19 @ X18 )
      | ( r2_hidden @ X18 @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) )
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
      | ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('80',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('86',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_waybel_7 @ X30 @ X29 @ X31 )
      | ~ ( v3_pre_topc @ X32 @ X30 )
      | ~ ( r2_hidden @ X31 @ X32 )
      | ( r2_hidden @ X32 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ sk_A )
      | ~ ( r2_waybel_7 @ sk_A @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ sk_A )
      | ~ ( r2_waybel_7 @ sk_A @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_waybel_7 @ sk_A @ X2 @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) )
      | ( r2_hidden @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ X2 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) )
      | ~ ( r2_waybel_7 @ sk_A @ X2 @ X1 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_waybel_7 @ sk_A @ X1 @ sk_B )
      | ( r2_hidden @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ X1 )
      | ~ ( r2_waybel_7 @ sk_A @ X1 @ sk_B )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['47','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('101',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('106',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('108',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('109',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('110',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('111',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['108','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('114',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('115',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['112','115'])).

thf(t11_waybel_7,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) )
     => ( ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ D @ A )
              & ( r2_hidden @ C @ B ) )
           => ( r2_hidden @ D @ B ) ) ) ) )).

thf('117',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v13_waybel_0 @ X33 @ ( k3_yellow_1 @ X34 ) )
      | ~ ( r2_hidden @ X35 @ X33 )
      | ~ ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X34 )
      | ( r2_hidden @ X36 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X34 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t11_waybel_7])).

thf('118',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('119',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('120',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v13_waybel_0 @ X33 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) )
      | ~ ( r2_hidden @ X35 @ X33 )
      | ~ ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_tarski @ X36 @ X34 )
      | ( r2_hidden @ X36 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( v13_waybel_0 @ sk_C_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['116','120'])).

thf('122',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,(
    v13_waybel_0 @ sk_C_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('125',plain,(
    v13_waybel_0 @ sk_C_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( v13_waybel_0 @ sk_C_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['113','114'])).

thf('128',plain,(
    v13_waybel_0 @ sk_C_2 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['121','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( r1_tarski @ X1 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['107','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 )
      | ~ ( r2_hidden @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ sk_C_2 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ sk_C_2 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['99','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('136',plain,
    ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 )
    | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['43','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PQSYGMKjSe
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:27:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 4.45/4.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.45/4.62  % Solved by: fo/fo7.sh
% 4.45/4.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.45/4.62  % done 4050 iterations in 4.156s
% 4.45/4.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.45/4.62  % SZS output start Refutation
% 4.45/4.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.45/4.62  thf(sk_A_type, type, sk_A: $i).
% 4.45/4.62  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 4.45/4.62  thf(r2_waybel_7_type, type, r2_waybel_7: $i > $i > $i > $o).
% 4.45/4.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.45/4.62  thf(k1_yellow19_type, type, k1_yellow19: $i > $i > $i).
% 4.45/4.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.45/4.62  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 4.45/4.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.45/4.62  thf(sk_B_type, type, sk_B: $i).
% 4.45/4.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 4.45/4.62  thf(sk_C_2_type, type, sk_C_2: $i).
% 4.45/4.62  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 4.45/4.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.45/4.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.45/4.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.45/4.62  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 4.45/4.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.45/4.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.45/4.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 4.45/4.62  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 4.45/4.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.45/4.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.45/4.62  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 4.45/4.62  thf(t4_yellow19, conjecture,
% 4.45/4.62    (![A:$i]:
% 4.45/4.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.45/4.62       ( ![B:$i]:
% 4.45/4.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.45/4.62           ( ![C:$i]:
% 4.45/4.62             ( ( ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 4.45/4.62                 ( m1_subset_1 @
% 4.45/4.62                   C @ 
% 4.45/4.62                   ( k1_zfmisc_1 @
% 4.45/4.62                     ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 4.45/4.62               ( ( r2_waybel_7 @ A @ C @ B ) <=>
% 4.45/4.62                 ( r1_tarski @ ( k1_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 4.45/4.62  thf(zf_stmt_0, negated_conjecture,
% 4.45/4.62    (~( ![A:$i]:
% 4.45/4.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.45/4.62            ( l1_pre_topc @ A ) ) =>
% 4.45/4.62          ( ![B:$i]:
% 4.45/4.62            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.45/4.62              ( ![C:$i]:
% 4.45/4.62                ( ( ( v13_waybel_0 @ C @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 4.45/4.62                    ( m1_subset_1 @
% 4.45/4.62                      C @ 
% 4.45/4.62                      ( k1_zfmisc_1 @
% 4.45/4.62                        ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 4.45/4.62                  ( ( r2_waybel_7 @ A @ C @ B ) <=>
% 4.45/4.62                    ( r1_tarski @ ( k1_yellow19 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 4.45/4.62    inference('cnf.neg', [status(esa)], [t4_yellow19])).
% 4.45/4.62  thf('0', plain,
% 4.45/4.62      ((~ (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)
% 4.45/4.62        | ~ (r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B))),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('1', plain,
% 4.45/4.62      ((~ (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2))
% 4.45/4.62         <= (~ ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)))),
% 4.45/4.62      inference('split', [status(esa)], ['0'])).
% 4.45/4.62  thf('2', plain,
% 4.45/4.62      (~ ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)) | 
% 4.45/4.62       ~ ((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B))),
% 4.45/4.62      inference('split', [status(esa)], ['0'])).
% 4.45/4.62  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf(d5_waybel_7, axiom,
% 4.45/4.62    (![A:$i]:
% 4.45/4.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.45/4.62       ( ![B:$i,C:$i]:
% 4.45/4.62         ( ( r2_waybel_7 @ A @ B @ C ) <=>
% 4.45/4.62           ( ![D:$i]:
% 4.45/4.62             ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.45/4.62               ( ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) ) =>
% 4.45/4.62                 ( r2_hidden @ D @ B ) ) ) ) ) ) ))).
% 4.45/4.62  thf('4', plain,
% 4.45/4.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.45/4.62         ((r2_hidden @ X28 @ (sk_D @ X28 @ X29 @ X30))
% 4.45/4.62          | (r2_waybel_7 @ X30 @ X29 @ X28)
% 4.45/4.62          | ~ (l1_pre_topc @ X30)
% 4.45/4.62          | ~ (v2_pre_topc @ X30))),
% 4.45/4.62      inference('cnf', [status(esa)], [d5_waybel_7])).
% 4.45/4.62  thf('5', plain,
% 4.45/4.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.45/4.62         ((v3_pre_topc @ (sk_D @ X28 @ X29 @ X30) @ X30)
% 4.45/4.62          | (r2_waybel_7 @ X30 @ X29 @ X28)
% 4.45/4.62          | ~ (l1_pre_topc @ X30)
% 4.45/4.62          | ~ (v2_pre_topc @ X30))),
% 4.45/4.62      inference('cnf', [status(esa)], [d5_waybel_7])).
% 4.45/4.62  thf('6', plain,
% 4.45/4.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.45/4.62         ((m1_subset_1 @ (sk_D @ X28 @ X29 @ X30) @ 
% 4.45/4.62           (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 4.45/4.62          | (r2_waybel_7 @ X30 @ X29 @ X28)
% 4.45/4.62          | ~ (l1_pre_topc @ X30)
% 4.45/4.62          | ~ (v2_pre_topc @ X30))),
% 4.45/4.62      inference('cnf', [status(esa)], [d5_waybel_7])).
% 4.45/4.62  thf(t5_connsp_2, axiom,
% 4.45/4.62    (![A:$i]:
% 4.45/4.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.45/4.62       ( ![B:$i]:
% 4.45/4.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.45/4.62           ( ![C:$i]:
% 4.45/4.62             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.45/4.62               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 4.45/4.62                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 4.45/4.62  thf('7', plain,
% 4.45/4.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.45/4.62         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 4.45/4.62          | ~ (v3_pre_topc @ X24 @ X25)
% 4.45/4.62          | ~ (r2_hidden @ X26 @ X24)
% 4.45/4.62          | (m1_connsp_2 @ X24 @ X25 @ X26)
% 4.45/4.62          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 4.45/4.62          | ~ (l1_pre_topc @ X25)
% 4.45/4.62          | ~ (v2_pre_topc @ X25)
% 4.45/4.62          | (v2_struct_0 @ X25))),
% 4.45/4.62      inference('cnf', [status(esa)], [t5_connsp_2])).
% 4.45/4.62  thf('8', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.45/4.62         (~ (v2_pre_topc @ X0)
% 4.45/4.62          | ~ (l1_pre_topc @ X0)
% 4.45/4.62          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 4.45/4.62          | (v2_struct_0 @ X0)
% 4.45/4.62          | ~ (v2_pre_topc @ X0)
% 4.45/4.62          | ~ (l1_pre_topc @ X0)
% 4.45/4.62          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 4.45/4.62          | (m1_connsp_2 @ (sk_D @ X2 @ X1 @ X0) @ X0 @ X3)
% 4.45/4.62          | ~ (r2_hidden @ X3 @ (sk_D @ X2 @ X1 @ X0))
% 4.45/4.62          | ~ (v3_pre_topc @ (sk_D @ X2 @ X1 @ X0) @ X0))),
% 4.45/4.62      inference('sup-', [status(thm)], ['6', '7'])).
% 4.45/4.62  thf('9', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.45/4.62         (~ (v3_pre_topc @ (sk_D @ X2 @ X1 @ X0) @ X0)
% 4.45/4.62          | ~ (r2_hidden @ X3 @ (sk_D @ X2 @ X1 @ X0))
% 4.45/4.62          | (m1_connsp_2 @ (sk_D @ X2 @ X1 @ X0) @ X0 @ X3)
% 4.45/4.62          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 4.45/4.62          | (v2_struct_0 @ X0)
% 4.45/4.62          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 4.45/4.62          | ~ (l1_pre_topc @ X0)
% 4.45/4.62          | ~ (v2_pre_topc @ X0))),
% 4.45/4.62      inference('simplify', [status(thm)], ['8'])).
% 4.45/4.62  thf('10', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.45/4.62         (~ (v2_pre_topc @ X0)
% 4.45/4.62          | ~ (l1_pre_topc @ X0)
% 4.45/4.62          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 4.45/4.62          | ~ (v2_pre_topc @ X0)
% 4.45/4.62          | ~ (l1_pre_topc @ X0)
% 4.45/4.62          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 4.45/4.62          | (v2_struct_0 @ X0)
% 4.45/4.62          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 4.45/4.62          | (m1_connsp_2 @ (sk_D @ X2 @ X1 @ X0) @ X0 @ X3)
% 4.45/4.62          | ~ (r2_hidden @ X3 @ (sk_D @ X2 @ X1 @ X0)))),
% 4.45/4.62      inference('sup-', [status(thm)], ['5', '9'])).
% 4.45/4.62  thf('11', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.45/4.62         (~ (r2_hidden @ X3 @ (sk_D @ X2 @ X1 @ X0))
% 4.45/4.62          | (m1_connsp_2 @ (sk_D @ X2 @ X1 @ X0) @ X0 @ X3)
% 4.45/4.62          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 4.45/4.62          | (v2_struct_0 @ X0)
% 4.45/4.62          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 4.45/4.62          | ~ (l1_pre_topc @ X0)
% 4.45/4.62          | ~ (v2_pre_topc @ X0))),
% 4.45/4.62      inference('simplify', [status(thm)], ['10'])).
% 4.45/4.62  thf('12', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.45/4.62         (~ (v2_pre_topc @ X0)
% 4.45/4.62          | ~ (l1_pre_topc @ X0)
% 4.45/4.62          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 4.45/4.62          | ~ (v2_pre_topc @ X0)
% 4.45/4.62          | ~ (l1_pre_topc @ X0)
% 4.45/4.62          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 4.45/4.62          | (v2_struct_0 @ X0)
% 4.45/4.62          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.45/4.62          | (m1_connsp_2 @ (sk_D @ X2 @ X1 @ X0) @ X0 @ X2))),
% 4.45/4.62      inference('sup-', [status(thm)], ['4', '11'])).
% 4.45/4.62  thf('13', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.45/4.62         ((m1_connsp_2 @ (sk_D @ X2 @ X1 @ X0) @ X0 @ X2)
% 4.45/4.62          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.45/4.62          | (v2_struct_0 @ X0)
% 4.45/4.62          | (r2_waybel_7 @ X0 @ X1 @ X2)
% 4.45/4.62          | ~ (l1_pre_topc @ X0)
% 4.45/4.62          | ~ (v2_pre_topc @ X0))),
% 4.45/4.62      inference('simplify', [status(thm)], ['12'])).
% 4.45/4.62  thf('14', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         (~ (v2_pre_topc @ sk_A)
% 4.45/4.62          | ~ (l1_pre_topc @ sk_A)
% 4.45/4.62          | (r2_waybel_7 @ sk_A @ X0 @ sk_B)
% 4.45/4.62          | (v2_struct_0 @ sk_A)
% 4.45/4.62          | (m1_connsp_2 @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A @ sk_B))),
% 4.45/4.62      inference('sup-', [status(thm)], ['3', '13'])).
% 4.45/4.62  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('17', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r2_waybel_7 @ sk_A @ X0 @ sk_B)
% 4.45/4.62          | (v2_struct_0 @ sk_A)
% 4.45/4.62          | (m1_connsp_2 @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A @ sk_B))),
% 4.45/4.62      inference('demod', [status(thm)], ['14', '15', '16'])).
% 4.45/4.62  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('19', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((m1_connsp_2 @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A @ sk_B)
% 4.45/4.62          | (r2_waybel_7 @ sk_A @ X0 @ sk_B))),
% 4.45/4.62      inference('clc', [status(thm)], ['17', '18'])).
% 4.45/4.62  thf('20', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf(t3_yellow19, axiom,
% 4.45/4.62    (![A:$i]:
% 4.45/4.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.45/4.62       ( ![B:$i]:
% 4.45/4.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.45/4.62           ( ![C:$i]:
% 4.45/4.62             ( ( r2_hidden @ C @ ( k1_yellow19 @ A @ B ) ) <=>
% 4.45/4.62               ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ))).
% 4.45/4.62  thf('21', plain,
% 4.45/4.62      (![X37 : $i, X38 : $i, X40 : $i]:
% 4.45/4.62         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 4.45/4.62          | ~ (m1_connsp_2 @ X40 @ X38 @ X37)
% 4.45/4.62          | (r2_hidden @ X40 @ (k1_yellow19 @ X38 @ X37))
% 4.45/4.62          | ~ (l1_pre_topc @ X38)
% 4.45/4.62          | ~ (v2_pre_topc @ X38)
% 4.45/4.62          | (v2_struct_0 @ X38))),
% 4.45/4.62      inference('cnf', [status(esa)], [t3_yellow19])).
% 4.45/4.62  thf('22', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((v2_struct_0 @ sk_A)
% 4.45/4.62          | ~ (v2_pre_topc @ sk_A)
% 4.45/4.62          | ~ (l1_pre_topc @ sk_A)
% 4.45/4.62          | (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B))
% 4.45/4.62          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 4.45/4.62      inference('sup-', [status(thm)], ['20', '21'])).
% 4.45/4.62  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('25', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((v2_struct_0 @ sk_A)
% 4.45/4.62          | (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B))
% 4.45/4.62          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 4.45/4.62      inference('demod', [status(thm)], ['22', '23', '24'])).
% 4.45/4.62  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('27', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 4.45/4.62          | (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))),
% 4.45/4.62      inference('clc', [status(thm)], ['25', '26'])).
% 4.45/4.62  thf('28', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r2_waybel_7 @ sk_A @ X0 @ sk_B)
% 4.45/4.62          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ 
% 4.45/4.62             (k1_yellow19 @ sk_A @ sk_B)))),
% 4.45/4.62      inference('sup-', [status(thm)], ['19', '27'])).
% 4.45/4.62  thf('29', plain,
% 4.45/4.62      (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)
% 4.45/4.62        | (r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B))),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('30', plain,
% 4.45/4.62      (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2))
% 4.45/4.62         <= (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)))),
% 4.45/4.62      inference('split', [status(esa)], ['29'])).
% 4.45/4.62  thf(d3_tarski, axiom,
% 4.45/4.62    (![A:$i,B:$i]:
% 4.45/4.62     ( ( r1_tarski @ A @ B ) <=>
% 4.45/4.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.45/4.62  thf('31', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.45/4.62         (~ (r2_hidden @ X0 @ X1)
% 4.45/4.62          | (r2_hidden @ X0 @ X2)
% 4.45/4.62          | ~ (r1_tarski @ X1 @ X2))),
% 4.45/4.62      inference('cnf', [status(esa)], [d3_tarski])).
% 4.45/4.62  thf('32', plain,
% 4.45/4.62      ((![X0 : $i]:
% 4.45/4.62          ((r2_hidden @ X0 @ sk_C_2)
% 4.45/4.62           | ~ (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B))))
% 4.45/4.62         <= (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)))),
% 4.45/4.62      inference('sup-', [status(thm)], ['30', '31'])).
% 4.45/4.62  thf('33', plain,
% 4.45/4.62      ((![X0 : $i]:
% 4.45/4.62          ((r2_waybel_7 @ sk_A @ X0 @ sk_B)
% 4.45/4.62           | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_C_2)))
% 4.45/4.62         <= (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)))),
% 4.45/4.62      inference('sup-', [status(thm)], ['28', '32'])).
% 4.45/4.62  thf('34', plain,
% 4.45/4.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.45/4.62         (~ (r2_hidden @ (sk_D @ X28 @ X29 @ X30) @ X29)
% 4.45/4.62          | (r2_waybel_7 @ X30 @ X29 @ X28)
% 4.45/4.62          | ~ (l1_pre_topc @ X30)
% 4.45/4.62          | ~ (v2_pre_topc @ X30))),
% 4.45/4.62      inference('cnf', [status(esa)], [d5_waybel_7])).
% 4.45/4.62  thf('35', plain,
% 4.45/4.62      ((((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)
% 4.45/4.62         | ~ (v2_pre_topc @ sk_A)
% 4.45/4.62         | ~ (l1_pre_topc @ sk_A)
% 4.45/4.62         | (r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)))
% 4.45/4.62         <= (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)))),
% 4.45/4.62      inference('sup-', [status(thm)], ['33', '34'])).
% 4.45/4.62  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('38', plain,
% 4.45/4.62      ((((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)
% 4.45/4.62         | (r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)))
% 4.45/4.62         <= (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)))),
% 4.45/4.62      inference('demod', [status(thm)], ['35', '36', '37'])).
% 4.45/4.62  thf('39', plain,
% 4.45/4.62      (((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B))
% 4.45/4.62         <= (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)))),
% 4.45/4.62      inference('simplify', [status(thm)], ['38'])).
% 4.45/4.62  thf('40', plain,
% 4.45/4.62      ((~ (r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B))
% 4.45/4.62         <= (~ ((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)))),
% 4.45/4.62      inference('split', [status(esa)], ['0'])).
% 4.45/4.62  thf('41', plain,
% 4.45/4.62      (((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)) | 
% 4.45/4.62       ~ ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2))),
% 4.45/4.62      inference('sup-', [status(thm)], ['39', '40'])).
% 4.45/4.62  thf('42', plain, (~ ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2))),
% 4.45/4.62      inference('sat_resolution*', [status(thm)], ['2', '41'])).
% 4.45/4.62  thf('43', plain, (~ (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)),
% 4.45/4.62      inference('simpl_trail', [status(thm)], ['1', '42'])).
% 4.45/4.62  thf('44', plain,
% 4.45/4.62      (((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B))
% 4.45/4.62         <= (((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)))),
% 4.45/4.62      inference('split', [status(esa)], ['29'])).
% 4.45/4.62  thf('45', plain,
% 4.45/4.62      (((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)) | 
% 4.45/4.62       ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2))),
% 4.45/4.62      inference('split', [status(esa)], ['29'])).
% 4.45/4.62  thf('46', plain, (((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B))),
% 4.45/4.62      inference('sat_resolution*', [status(thm)], ['2', '41', '45'])).
% 4.45/4.62  thf('47', plain, ((r2_waybel_7 @ sk_A @ sk_C_2 @ sk_B)),
% 4.45/4.62      inference('simpl_trail', [status(thm)], ['44', '46'])).
% 4.45/4.62  thf('48', plain,
% 4.45/4.62      (![X1 : $i, X3 : $i]:
% 4.45/4.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.45/4.62      inference('cnf', [status(esa)], [d3_tarski])).
% 4.45/4.62  thf('49', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('50', plain,
% 4.45/4.62      (![X37 : $i, X38 : $i, X39 : $i]:
% 4.45/4.62         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 4.45/4.62          | ~ (r2_hidden @ X39 @ (k1_yellow19 @ X38 @ X37))
% 4.45/4.62          | (m1_connsp_2 @ X39 @ X38 @ X37)
% 4.45/4.62          | ~ (l1_pre_topc @ X38)
% 4.45/4.62          | ~ (v2_pre_topc @ X38)
% 4.45/4.62          | (v2_struct_0 @ X38))),
% 4.45/4.62      inference('cnf', [status(esa)], [t3_yellow19])).
% 4.45/4.62  thf('51', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((v2_struct_0 @ sk_A)
% 4.45/4.62          | ~ (v2_pre_topc @ sk_A)
% 4.45/4.62          | ~ (l1_pre_topc @ sk_A)
% 4.45/4.62          | (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 4.45/4.62          | ~ (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))),
% 4.45/4.62      inference('sup-', [status(thm)], ['49', '50'])).
% 4.45/4.62  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('54', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((v2_struct_0 @ sk_A)
% 4.45/4.62          | (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 4.45/4.62          | ~ (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))),
% 4.45/4.62      inference('demod', [status(thm)], ['51', '52', '53'])).
% 4.45/4.62  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('56', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         (~ (r2_hidden @ X0 @ (k1_yellow19 @ sk_A @ sk_B))
% 4.45/4.62          | (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 4.45/4.62      inference('clc', [status(thm)], ['54', '55'])).
% 4.45/4.62  thf('57', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_A @ 
% 4.45/4.62             sk_B))),
% 4.45/4.62      inference('sup-', [status(thm)], ['48', '56'])).
% 4.45/4.62  thf('58', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_A @ 
% 4.45/4.62             sk_B))),
% 4.45/4.62      inference('sup-', [status(thm)], ['48', '56'])).
% 4.45/4.62  thf('59', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf(dt_m1_connsp_2, axiom,
% 4.45/4.62    (![A:$i,B:$i]:
% 4.45/4.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.45/4.62         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 4.45/4.62       ( ![C:$i]:
% 4.45/4.62         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 4.45/4.62           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 4.45/4.62  thf('60', plain,
% 4.45/4.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.45/4.62         (~ (l1_pre_topc @ X21)
% 4.45/4.62          | ~ (v2_pre_topc @ X21)
% 4.45/4.62          | (v2_struct_0 @ X21)
% 4.45/4.62          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 4.45/4.62          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 4.45/4.62          | ~ (m1_connsp_2 @ X23 @ X21 @ X22))),
% 4.45/4.62      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 4.45/4.62  thf('61', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 4.45/4.62          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.45/4.62          | (v2_struct_0 @ sk_A)
% 4.45/4.62          | ~ (v2_pre_topc @ sk_A)
% 4.45/4.62          | ~ (l1_pre_topc @ sk_A))),
% 4.45/4.62      inference('sup-', [status(thm)], ['59', '60'])).
% 4.45/4.62  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('64', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 4.45/4.62          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.45/4.62          | (v2_struct_0 @ sk_A))),
% 4.45/4.62      inference('demod', [status(thm)], ['61', '62', '63'])).
% 4.45/4.62  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('66', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.45/4.62          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 4.45/4.62      inference('clc', [status(thm)], ['64', '65'])).
% 4.45/4.62  thf('67', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (m1_subset_1 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 4.45/4.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.45/4.62      inference('sup-', [status(thm)], ['58', '66'])).
% 4.45/4.62  thf(d1_connsp_2, axiom,
% 4.45/4.62    (![A:$i]:
% 4.45/4.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.45/4.62       ( ![B:$i]:
% 4.45/4.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.45/4.62           ( ![C:$i]:
% 4.45/4.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.45/4.62               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 4.45/4.62                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 4.45/4.62  thf('68', plain,
% 4.45/4.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.45/4.62         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 4.45/4.62          | ~ (m1_connsp_2 @ X20 @ X19 @ X18)
% 4.45/4.62          | (r2_hidden @ X18 @ (k1_tops_1 @ X19 @ X20))
% 4.45/4.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 4.45/4.62          | ~ (l1_pre_topc @ X19)
% 4.45/4.62          | ~ (v2_pre_topc @ X19)
% 4.45/4.62          | (v2_struct_0 @ X19))),
% 4.45/4.62      inference('cnf', [status(esa)], [d1_connsp_2])).
% 4.45/4.62  thf('69', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (v2_struct_0 @ sk_A)
% 4.45/4.62          | ~ (v2_pre_topc @ sk_A)
% 4.45/4.62          | ~ (l1_pre_topc @ sk_A)
% 4.45/4.62          | (r2_hidden @ X1 @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))))
% 4.45/4.62          | ~ (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 4.45/4.62               sk_A @ X1)
% 4.45/4.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 4.45/4.62      inference('sup-', [status(thm)], ['67', '68'])).
% 4.45/4.62  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('72', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (v2_struct_0 @ sk_A)
% 4.45/4.62          | (r2_hidden @ X1 @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))))
% 4.45/4.62          | ~ (m1_connsp_2 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 4.45/4.62               sk_A @ X1)
% 4.45/4.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 4.45/4.62      inference('demod', [status(thm)], ['69', '70', '71'])).
% 4.45/4.62  thf('73', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 4.45/4.62          | (r2_hidden @ sk_B @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))))
% 4.45/4.62          | (v2_struct_0 @ sk_A)
% 4.45/4.62          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 4.45/4.62      inference('sup-', [status(thm)], ['57', '72'])).
% 4.45/4.62  thf('74', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('75', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (r2_hidden @ sk_B @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))))
% 4.45/4.62          | (v2_struct_0 @ sk_A)
% 4.45/4.62          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 4.45/4.62      inference('demod', [status(thm)], ['73', '74'])).
% 4.45/4.62  thf('76', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((v2_struct_0 @ sk_A)
% 4.45/4.62          | (r2_hidden @ sk_B @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))))
% 4.45/4.62          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 4.45/4.62      inference('simplify', [status(thm)], ['75'])).
% 4.45/4.62  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('78', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (r2_hidden @ sk_B @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))))),
% 4.45/4.62      inference('clc', [status(thm)], ['76', '77'])).
% 4.45/4.62  thf('79', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (m1_subset_1 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 4.45/4.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.45/4.62      inference('sup-', [status(thm)], ['58', '66'])).
% 4.45/4.62  thf(fc9_tops_1, axiom,
% 4.45/4.62    (![A:$i,B:$i]:
% 4.45/4.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 4.45/4.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.45/4.62       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 4.45/4.62  thf('80', plain,
% 4.45/4.62      (![X14 : $i, X15 : $i]:
% 4.45/4.62         (~ (l1_pre_topc @ X14)
% 4.45/4.62          | ~ (v2_pre_topc @ X14)
% 4.45/4.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 4.45/4.62          | (v3_pre_topc @ (k1_tops_1 @ X14 @ X15) @ X14))),
% 4.45/4.62      inference('cnf', [status(esa)], [fc9_tops_1])).
% 4.45/4.62  thf('81', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (v3_pre_topc @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62             sk_A)
% 4.45/4.62          | ~ (v2_pre_topc @ sk_A)
% 4.45/4.62          | ~ (l1_pre_topc @ sk_A))),
% 4.45/4.62      inference('sup-', [status(thm)], ['79', '80'])).
% 4.45/4.62  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('84', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (v3_pre_topc @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62             sk_A))),
% 4.45/4.62      inference('demod', [status(thm)], ['81', '82', '83'])).
% 4.45/4.62  thf('85', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (m1_subset_1 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 4.45/4.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.45/4.62      inference('sup-', [status(thm)], ['58', '66'])).
% 4.45/4.62  thf(dt_k1_tops_1, axiom,
% 4.45/4.62    (![A:$i,B:$i]:
% 4.45/4.62     ( ( ( l1_pre_topc @ A ) & 
% 4.45/4.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.45/4.62       ( m1_subset_1 @
% 4.45/4.62         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.45/4.62  thf('86', plain,
% 4.45/4.62      (![X12 : $i, X13 : $i]:
% 4.45/4.62         (~ (l1_pre_topc @ X12)
% 4.45/4.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 4.45/4.62          | (m1_subset_1 @ (k1_tops_1 @ X12 @ X13) @ 
% 4.45/4.62             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 4.45/4.62      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 4.45/4.62  thf('87', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (m1_subset_1 @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.45/4.62          | ~ (l1_pre_topc @ sk_A))),
% 4.45/4.62      inference('sup-', [status(thm)], ['85', '86'])).
% 4.45/4.62  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('89', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (m1_subset_1 @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.45/4.62      inference('demod', [status(thm)], ['87', '88'])).
% 4.45/4.62  thf('90', plain,
% 4.45/4.62      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 4.45/4.62         (~ (r2_waybel_7 @ X30 @ X29 @ X31)
% 4.45/4.62          | ~ (v3_pre_topc @ X32 @ X30)
% 4.45/4.62          | ~ (r2_hidden @ X31 @ X32)
% 4.45/4.62          | (r2_hidden @ X32 @ X29)
% 4.45/4.62          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 4.45/4.62          | ~ (l1_pre_topc @ X30)
% 4.45/4.62          | ~ (v2_pre_topc @ X30))),
% 4.45/4.62      inference('cnf', [status(esa)], [d5_waybel_7])).
% 4.45/4.62  thf('91', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | ~ (v2_pre_topc @ sk_A)
% 4.45/4.62          | ~ (l1_pre_topc @ sk_A)
% 4.45/4.62          | (r2_hidden @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62             X1)
% 4.45/4.62          | ~ (r2_hidden @ X2 @ 
% 4.45/4.62               (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))))
% 4.45/4.62          | ~ (v3_pre_topc @ 
% 4.45/4.62               (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62               sk_A)
% 4.45/4.62          | ~ (r2_waybel_7 @ sk_A @ X1 @ X2))),
% 4.45/4.62      inference('sup-', [status(thm)], ['89', '90'])).
% 4.45/4.62  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('94', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (r2_hidden @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62             X1)
% 4.45/4.62          | ~ (r2_hidden @ X2 @ 
% 4.45/4.62               (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))))
% 4.45/4.62          | ~ (v3_pre_topc @ 
% 4.45/4.62               (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62               sk_A)
% 4.45/4.62          | ~ (r2_waybel_7 @ sk_A @ X1 @ X2))),
% 4.45/4.62      inference('demod', [status(thm)], ['91', '92', '93'])).
% 4.45/4.62  thf('95', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | ~ (r2_waybel_7 @ sk_A @ X2 @ X1)
% 4.45/4.62          | ~ (r2_hidden @ X1 @ 
% 4.45/4.62               (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))))
% 4.45/4.62          | (r2_hidden @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62             X2)
% 4.45/4.62          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 4.45/4.62      inference('sup-', [status(thm)], ['84', '94'])).
% 4.45/4.62  thf('96', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.45/4.62         ((r2_hidden @ 
% 4.45/4.62           (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ X2)
% 4.45/4.62          | ~ (r2_hidden @ X1 @ 
% 4.45/4.62               (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))))
% 4.45/4.62          | ~ (r2_waybel_7 @ sk_A @ X2 @ X1)
% 4.45/4.62          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 4.45/4.62      inference('simplify', [status(thm)], ['95'])).
% 4.45/4.62  thf('97', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | ~ (r2_waybel_7 @ sk_A @ X1 @ sk_B)
% 4.45/4.62          | (r2_hidden @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62             X1))),
% 4.45/4.62      inference('sup-', [status(thm)], ['78', '96'])).
% 4.45/4.62  thf('98', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i]:
% 4.45/4.62         ((r2_hidden @ 
% 4.45/4.62           (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ X1)
% 4.45/4.62          | ~ (r2_waybel_7 @ sk_A @ X1 @ sk_B)
% 4.45/4.62          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 4.45/4.62      inference('simplify', [status(thm)], ['97'])).
% 4.45/4.62  thf('99', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (r2_hidden @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62             sk_C_2))),
% 4.45/4.62      inference('sup-', [status(thm)], ['47', '98'])).
% 4.45/4.62  thf('100', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (m1_subset_1 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 4.45/4.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.45/4.62      inference('sup-', [status(thm)], ['58', '66'])).
% 4.45/4.62  thf(t44_tops_1, axiom,
% 4.45/4.62    (![A:$i]:
% 4.45/4.62     ( ( l1_pre_topc @ A ) =>
% 4.45/4.62       ( ![B:$i]:
% 4.45/4.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.45/4.62           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 4.45/4.62  thf('101', plain,
% 4.45/4.62      (![X16 : $i, X17 : $i]:
% 4.45/4.62         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 4.45/4.62          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 4.45/4.62          | ~ (l1_pre_topc @ X17))),
% 4.45/4.62      inference('cnf', [status(esa)], [t44_tops_1])).
% 4.45/4.62  thf('102', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | ~ (l1_pre_topc @ sk_A)
% 4.45/4.62          | (r1_tarski @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62             (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))))),
% 4.45/4.62      inference('sup-', [status(thm)], ['100', '101'])).
% 4.45/4.62  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('104', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (r1_tarski @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62             (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))))),
% 4.45/4.62      inference('demod', [status(thm)], ['102', '103'])).
% 4.45/4.62  thf('105', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (m1_subset_1 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 4.45/4.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.45/4.62      inference('sup-', [status(thm)], ['58', '66'])).
% 4.45/4.62  thf(t3_subset, axiom,
% 4.45/4.62    (![A:$i,B:$i]:
% 4.45/4.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.45/4.62  thf('106', plain,
% 4.45/4.62      (![X4 : $i, X5 : $i]:
% 4.45/4.62         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 4.45/4.62      inference('cnf', [status(esa)], [t3_subset])).
% 4.45/4.62  thf('107', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (r1_tarski @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ 
% 4.45/4.62             (u1_struct_0 @ sk_A)))),
% 4.45/4.62      inference('sup-', [status(thm)], ['105', '106'])).
% 4.45/4.62  thf(d3_struct_0, axiom,
% 4.45/4.62    (![A:$i]:
% 4.45/4.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 4.45/4.62  thf('108', plain,
% 4.45/4.62      (![X10 : $i]:
% 4.45/4.62         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 4.45/4.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.45/4.62  thf('109', plain,
% 4.45/4.62      ((m1_subset_1 @ sk_C_2 @ 
% 4.45/4.62        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf(d2_yellow_1, axiom,
% 4.45/4.62    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 4.45/4.62  thf('110', plain,
% 4.45/4.62      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 4.45/4.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 4.45/4.62  thf('111', plain,
% 4.45/4.62      ((m1_subset_1 @ sk_C_2 @ 
% 4.45/4.62        (k1_zfmisc_1 @ 
% 4.45/4.62         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 4.45/4.62      inference('demod', [status(thm)], ['109', '110'])).
% 4.45/4.62  thf('112', plain,
% 4.45/4.62      (((m1_subset_1 @ sk_C_2 @ 
% 4.45/4.62         (k1_zfmisc_1 @ 
% 4.45/4.62          (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))
% 4.45/4.62        | ~ (l1_struct_0 @ sk_A))),
% 4.45/4.62      inference('sup+', [status(thm)], ['108', '111'])).
% 4.45/4.62  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf(dt_l1_pre_topc, axiom,
% 4.45/4.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 4.45/4.62  thf('114', plain,
% 4.45/4.62      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 4.45/4.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 4.45/4.62  thf('115', plain, ((l1_struct_0 @ sk_A)),
% 4.45/4.62      inference('sup-', [status(thm)], ['113', '114'])).
% 4.45/4.62  thf('116', plain,
% 4.45/4.62      ((m1_subset_1 @ sk_C_2 @ 
% 4.45/4.62        (k1_zfmisc_1 @ 
% 4.45/4.62         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))))),
% 4.45/4.62      inference('demod', [status(thm)], ['112', '115'])).
% 4.45/4.62  thf(t11_waybel_7, axiom,
% 4.45/4.62    (![A:$i,B:$i]:
% 4.45/4.62     ( ( m1_subset_1 @
% 4.45/4.62         B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) =>
% 4.45/4.62       ( ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) <=>
% 4.45/4.62         ( ![C:$i,D:$i]:
% 4.45/4.62           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ D @ A ) & 
% 4.45/4.62               ( r2_hidden @ C @ B ) ) =>
% 4.45/4.62             ( r2_hidden @ D @ B ) ) ) ) ))).
% 4.45/4.62  thf('117', plain,
% 4.45/4.62      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 4.45/4.62         (~ (v13_waybel_0 @ X33 @ (k3_yellow_1 @ X34))
% 4.45/4.62          | ~ (r2_hidden @ X35 @ X33)
% 4.45/4.62          | ~ (r1_tarski @ X35 @ X36)
% 4.45/4.62          | ~ (r1_tarski @ X36 @ X34)
% 4.45/4.62          | (r2_hidden @ X36 @ X33)
% 4.45/4.62          | ~ (m1_subset_1 @ X33 @ 
% 4.45/4.62               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X34)))))),
% 4.45/4.62      inference('cnf', [status(esa)], [t11_waybel_7])).
% 4.45/4.62  thf('118', plain,
% 4.45/4.62      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 4.45/4.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 4.45/4.62  thf('119', plain,
% 4.45/4.62      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 4.45/4.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 4.45/4.62  thf('120', plain,
% 4.45/4.62      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 4.45/4.62         (~ (v13_waybel_0 @ X33 @ (k3_lattice3 @ (k1_lattice3 @ X34)))
% 4.45/4.62          | ~ (r2_hidden @ X35 @ X33)
% 4.45/4.62          | ~ (r1_tarski @ X35 @ X36)
% 4.45/4.62          | ~ (r1_tarski @ X36 @ X34)
% 4.45/4.62          | (r2_hidden @ X36 @ X33)
% 4.45/4.62          | ~ (m1_subset_1 @ X33 @ 
% 4.45/4.62               (k1_zfmisc_1 @ 
% 4.45/4.62                (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X34))))))),
% 4.45/4.62      inference('demod', [status(thm)], ['117', '118', '119'])).
% 4.45/4.62  thf('121', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i]:
% 4.45/4.62         ((r2_hidden @ X0 @ sk_C_2)
% 4.45/4.62          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A))
% 4.45/4.62          | ~ (r1_tarski @ X1 @ X0)
% 4.45/4.62          | ~ (r2_hidden @ X1 @ sk_C_2)
% 4.45/4.62          | ~ (v13_waybel_0 @ sk_C_2 @ 
% 4.45/4.62               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A)))))),
% 4.45/4.62      inference('sup-', [status(thm)], ['116', '120'])).
% 4.45/4.62  thf('122', plain,
% 4.45/4.62      (![X10 : $i]:
% 4.45/4.62         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 4.45/4.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.45/4.62  thf('123', plain,
% 4.45/4.62      ((v13_waybel_0 @ sk_C_2 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 4.45/4.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.45/4.62  thf('124', plain,
% 4.45/4.62      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 4.45/4.62      inference('cnf', [status(esa)], [d2_yellow_1])).
% 4.45/4.62  thf('125', plain,
% 4.45/4.62      ((v13_waybel_0 @ sk_C_2 @ 
% 4.45/4.62        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 4.45/4.62      inference('demod', [status(thm)], ['123', '124'])).
% 4.45/4.62  thf('126', plain,
% 4.45/4.62      (((v13_waybel_0 @ sk_C_2 @ 
% 4.45/4.62         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 4.45/4.62        | ~ (l1_struct_0 @ sk_A))),
% 4.45/4.62      inference('sup+', [status(thm)], ['122', '125'])).
% 4.45/4.62  thf('127', plain, ((l1_struct_0 @ sk_A)),
% 4.45/4.62      inference('sup-', [status(thm)], ['113', '114'])).
% 4.45/4.62  thf('128', plain,
% 4.45/4.62      ((v13_waybel_0 @ sk_C_2 @ 
% 4.45/4.62        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 4.45/4.62      inference('demod', [status(thm)], ['126', '127'])).
% 4.45/4.62  thf('129', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i]:
% 4.45/4.62         ((r2_hidden @ X0 @ sk_C_2)
% 4.45/4.62          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A))
% 4.45/4.62          | ~ (r1_tarski @ X1 @ X0)
% 4.45/4.62          | ~ (r2_hidden @ X1 @ sk_C_2))),
% 4.45/4.62      inference('demod', [status(thm)], ['121', '128'])).
% 4.45/4.62  thf('130', plain,
% 4.45/4.62      (![X0 : $i, X1 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | ~ (r2_hidden @ X1 @ sk_C_2)
% 4.45/4.62          | ~ (r1_tarski @ X1 @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)))
% 4.45/4.62          | (r2_hidden @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_C_2))),
% 4.45/4.62      inference('sup-', [status(thm)], ['107', '129'])).
% 4.45/4.62  thf('131', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (r2_hidden @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_C_2)
% 4.45/4.62          | ~ (r2_hidden @ 
% 4.45/4.62               (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62               sk_C_2)
% 4.45/4.62          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 4.45/4.62      inference('sup-', [status(thm)], ['104', '130'])).
% 4.45/4.62  thf('132', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         (~ (r2_hidden @ 
% 4.45/4.62             (k1_tops_1 @ sk_A @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B))) @ 
% 4.45/4.62             sk_C_2)
% 4.45/4.62          | (r2_hidden @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_C_2)
% 4.45/4.62          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 4.45/4.62      inference('simplify', [status(thm)], ['131'])).
% 4.45/4.62  thf('133', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0)
% 4.45/4.62          | (r2_hidden @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_C_2))),
% 4.45/4.62      inference('sup-', [status(thm)], ['99', '132'])).
% 4.45/4.62  thf('134', plain,
% 4.45/4.62      (![X0 : $i]:
% 4.45/4.62         ((r2_hidden @ (sk_C @ X0 @ (k1_yellow19 @ sk_A @ sk_B)) @ sk_C_2)
% 4.45/4.62          | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ X0))),
% 4.45/4.62      inference('simplify', [status(thm)], ['133'])).
% 4.45/4.62  thf('135', plain,
% 4.45/4.62      (![X1 : $i, X3 : $i]:
% 4.45/4.62         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.45/4.62      inference('cnf', [status(esa)], [d3_tarski])).
% 4.45/4.62  thf('136', plain,
% 4.45/4.62      (((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)
% 4.45/4.62        | (r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2))),
% 4.45/4.62      inference('sup-', [status(thm)], ['134', '135'])).
% 4.45/4.62  thf('137', plain, ((r1_tarski @ (k1_yellow19 @ sk_A @ sk_B) @ sk_C_2)),
% 4.45/4.62      inference('simplify', [status(thm)], ['136'])).
% 4.45/4.62  thf('138', plain, ($false), inference('demod', [status(thm)], ['43', '137'])).
% 4.45/4.62  
% 4.45/4.62  % SZS output end Refutation
% 4.45/4.62  
% 4.45/4.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
