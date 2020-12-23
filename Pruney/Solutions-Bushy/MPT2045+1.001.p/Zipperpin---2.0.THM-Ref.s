%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2045+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HgtN2rH2xy

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:42 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 500 expanded)
%              Number of leaves         :   36 ( 152 expanded)
%              Depth                    :   24
%              Number of atoms          : 1860 (8930 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_yellow19_type,type,(
    k1_yellow19: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_waybel_7_type,type,(
    r2_waybel_7: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( sk_D @ X8 @ X9 @ X10 ) )
      | ( r2_waybel_7 @ X10 @ X9 @ X8 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v3_pre_topc @ ( sk_D @ X8 @ X9 @ X10 ) @ X10 )
      | ( r2_waybel_7 @ X10 @ X9 @ X8 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_waybel_7])).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r2_waybel_7 @ X10 @ X9 @ X8 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v3_pre_topc @ X34 @ X35 )
      | ~ ( r2_hidden @ X36 @ X34 )
      | ( m1_connsp_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
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
    ! [X28: $i,X29: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_connsp_2 @ X31 @ X29 @ X28 )
      | ( r2_hidden @ X31 @ ( k1_yellow19 @ X29 @ X28 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X8 @ X9 @ X10 ) @ X9 )
      | ( r2_waybel_7 @ X10 @ X9 @ X8 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
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
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r2_hidden @ X30 @ ( k1_yellow19 @ X29 @ X28 ) )
      | ( m1_connsp_2 @ X30 @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_connsp_2 @ X18 @ X16 @ X17 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_connsp_2 @ X2 @ X1 @ X0 )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X19 @ X20 ) @ X19 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_waybel_7 @ X10 @ X9 @ X11 )
      | ~ ( v3_pre_topc @ X12 @ X10 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X33 @ X32 ) @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
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
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('109',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('112',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('113',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['110','113'])).

thf(t11_waybel_7,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) )
     => ( ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ D @ A )
              & ( r2_hidden @ C @ B ) )
           => ( r2_hidden @ D @ B ) ) ) ) )).

thf('115',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( v13_waybel_0 @ X21 @ ( k3_yellow_1 @ X22 ) )
      | ~ ( r2_hidden @ X23 @ X21 )
      | ~ ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ( r2_hidden @ X24 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X22 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t11_waybel_7])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( v13_waybel_0 @ sk_C_2 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,(
    v13_waybel_0 @ sk_C_2 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v13_waybel_0 @ sk_C_2 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['111','112'])).

thf('121',plain,(
    v13_waybel_0 @ sk_C_2 @ ( k3_yellow_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['116','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_C_2 )
      | ~ ( r1_tarski @ X1 @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['107','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 )
      | ~ ( r2_hidden @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ sk_C_2 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_tops_1 @ sk_A @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) ) @ sk_C_2 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['99','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_yellow19 @ sk_A @ sk_B ) ) @ sk_C_2 )
      | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('129',plain,
    ( ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 )
    | ( r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    r1_tarski @ ( k1_yellow19 @ sk_A @ sk_B ) @ sk_C_2 ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['43','130'])).


%------------------------------------------------------------------------------
