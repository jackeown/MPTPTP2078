%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2066+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y0uE66zsVn

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:44 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  227 (1445 expanded)
%              Number of leaves         :   30 ( 409 expanded)
%              Depth                    :   34
%              Number of atoms          : 3941 (34812 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t26_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( v4_orders_2 @ C )
                  & ( v7_waybel_0 @ C )
                  & ( v3_yellow_6 @ C @ A )
                  & ( l1_waybel_0 @ C @ A ) )
               => ( ( r1_waybel_0 @ A @ C @ B )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ ( k10_yellow_6 @ A @ C ) )
                       => ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v4_orders_2 @ C )
                    & ( v7_waybel_0 @ C )
                    & ( v3_yellow_6 @ C @ A )
                    & ( l1_waybel_0 @ C @ A ) )
                 => ( ( r1_waybel_0 @ A @ C @ B )
                   => ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ( ( r2_hidden @ D @ ( k10_yellow_6 @ A @ C ) )
                         => ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_yellow19])).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( v3_yellow_6 @ X20 @ sk_A )
      | ~ ( l1_waybel_0 @ X20 @ sk_A )
      | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
      | ( r2_hidden @ X21 @ sk_B )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ D ) )
                    & ( r1_waybel_0 @ A @ D @ B )
                    & ( l1_waybel_0 @ D @ A )
                    & ( v3_yellow_6 @ D @ A )
                    & ( v7_waybel_0 @ D )
                    & ( v4_orders_2 @ D )
                    & ~ ( v2_struct_0 @ D ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ( v4_orders_2 @ ( sk_D @ X11 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v4_orders_2 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v4_orders_2 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v4_orders_2 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v4_orders_2 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('25',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ( v7_waybel_0 @ ( sk_D @ X11 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v7_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v7_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v7_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('38',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ( v3_yellow_6 @ ( sk_D @ X11 @ X9 @ X10 ) @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v3_yellow_6 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('51',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ( l1_waybel_0 @ ( sk_D @ X11 @ X9 @ X10 ) @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( l1_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( l1_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('64',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ( r1_waybel_0 @ X10 @ ( sk_D @ X11 @ X9 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_waybel_0 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r1_waybel_0 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_waybel_0 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r1_waybel_0 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('77',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ( r2_hidden @ X11 @ ( k10_yellow_6 @ X10 @ ( sk_D @ X11 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('90',plain,
    ( ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_waybel_0 @ sk_A @ X1 @ sk_B )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
        | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k10_yellow_6 @ sk_A @ X1 ) )
        | ~ ( l1_waybel_0 @ X1 @ sk_A )
        | ~ ( v3_yellow_6 @ X1 @ sk_A )
        | ~ ( v7_waybel_0 @ X1 )
        | ~ ( v4_orders_2 @ X1 )
        | ( v2_struct_0 @ X1 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( v2_struct_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v3_yellow_6 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
        | ~ ( l1_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_waybel_0 @ sk_A @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
        | ~ ( l1_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
        | ~ ( v3_yellow_6 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
        | ~ ( v7_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( v2_struct_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v3_yellow_6 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
        | ~ ( l1_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','93'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
        | ~ ( l1_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
        | ~ ( v3_yellow_6 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
        | ~ ( v7_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( v2_struct_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v3_yellow_6 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
        | ~ ( v3_yellow_6 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_A )
        | ~ ( v7_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( v2_struct_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','97'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
        | ~ ( v7_waybel_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( v2_struct_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','99'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
        | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( v2_struct_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','101'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
        | ( v2_struct_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ~ ( v2_struct_0 @ ( sk_D @ X11 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( v2_struct_0 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','113'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
        | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('119',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('122',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ X13 @ ( k2_pre_topc @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('123',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('126',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('127',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','127'])).

thf('129',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('130',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_pre_topc @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
       != X18 )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('131',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B )
       != ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','134'])).

thf('136',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','127'])).

thf('137',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','127'])).

thf('138',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','127'])).

thf('139',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','136','137','138'])).

thf('140',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ! [X20: $i,X21: $i] :
        ( ( v2_struct_0 @ X20 )
        | ~ ( v4_orders_2 @ X20 )
        | ~ ( v7_waybel_0 @ X20 )
        | ~ ( v3_yellow_6 @ X20 @ sk_A )
        | ~ ( l1_waybel_0 @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
        | ( r2_hidden @ X21 @ sk_B )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['141'])).

thf('143',plain,
    ( ~ ! [X20: $i,X21: $i] :
          ( ( v2_struct_0 @ X20 )
          | ~ ( v4_orders_2 @ X20 )
          | ~ ( v7_waybel_0 @ X20 )
          | ~ ( v3_yellow_6 @ X20 @ sk_A )
          | ~ ( l1_waybel_0 @ X20 @ sk_A )
          | ~ ( r2_hidden @ X21 @ ( k10_yellow_6 @ sk_A @ X20 ) )
          | ( r2_hidden @ X21 @ sk_B )
          | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r1_waybel_0 @ sk_A @ X20 @ sk_B ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['140','142'])).

thf('144',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['141'])).

thf('145',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['145'])).

thf('147',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['147'])).

thf('149',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['149'])).

thf('151',plain,
    ( ( l1_waybel_0 @ sk_C_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( l1_waybel_0 @ sk_C_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['151'])).

thf('153',plain,
    ( ( v3_yellow_6 @ sk_C_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v3_yellow_6 @ sk_C_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['153'])).

thf('155',plain,
    ( ( v7_waybel_0 @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v7_waybel_0 @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['155'])).

thf('157',plain,
    ( ( v4_orders_2 @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v4_orders_2 @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['157'])).

thf('159',plain,
    ( ~ ( v2_struct_0 @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ~ ( v2_struct_0 @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['159'])).

thf('161',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('162',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_pre_topc @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('164',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['161','166'])).

thf('168',plain,
    ( ( v4_orders_2 @ sk_C_1 )
   <= ( v4_orders_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['157'])).

thf('169',plain,
    ( ( v7_waybel_0 @ sk_C_1 )
   <= ( v7_waybel_0 @ sk_C_1 ) ),
    inference(split,[status(esa)],['155'])).

thf('170',plain,
    ( ( v3_yellow_6 @ sk_C_1 @ sk_A )
   <= ( v3_yellow_6 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['153'])).

thf('171',plain,
    ( ( l1_waybel_0 @ sk_C_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['151'])).

thf('172',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_C_1 @ sk_B )
   <= ( r1_waybel_0 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['141'])).

thf('173',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['149'])).

thf('174',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['145'])).

thf('175',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k10_yellow_6 @ X10 @ X12 ) )
      | ~ ( r1_waybel_0 @ X10 @ X12 @ X9 )
      | ~ ( l1_waybel_0 @ X12 @ X10 )
      | ~ ( v3_yellow_6 @ X12 @ X10 )
      | ~ ( v7_waybel_0 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_yellow19])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( v3_yellow_6 @ X1 @ sk_A )
      | ~ ( l1_waybel_0 @ X1 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( v3_yellow_6 @ X1 @ sk_A )
      | ~ ( l1_waybel_0 @ X1 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ X1 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ X1 ) ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ X0 ) )
        | ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_B )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v3_yellow_6 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( r2_hidden @ sk_D_1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['174','180'])).

thf('182',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_D_1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( v4_orders_2 @ sk_C_1 )
      | ~ ( v7_waybel_0 @ sk_C_1 )
      | ~ ( v3_yellow_6 @ sk_C_1 @ sk_A )
      | ~ ( l1_waybel_0 @ sk_C_1 @ sk_A )
      | ~ ( r1_waybel_0 @ sk_A @ sk_C_1 @ sk_B ) )
   <= ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['173','181'])).

thf('183',plain,
    ( ( ~ ( l1_waybel_0 @ sk_C_1 @ sk_A )
      | ~ ( v3_yellow_6 @ sk_C_1 @ sk_A )
      | ~ ( v7_waybel_0 @ sk_C_1 )
      | ~ ( v4_orders_2 @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r2_hidden @ sk_D_1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r1_waybel_0 @ sk_A @ sk_C_1 @ sk_B )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['172','182'])).

thf('184',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_D_1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( v4_orders_2 @ sk_C_1 )
      | ~ ( v7_waybel_0 @ sk_C_1 )
      | ~ ( v3_yellow_6 @ sk_C_1 @ sk_A ) )
   <= ( ( r1_waybel_0 @ sk_A @ sk_C_1 @ sk_B )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      & ( l1_waybel_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['171','183'])).

thf('185',plain,
    ( ( ~ ( v7_waybel_0 @ sk_C_1 )
      | ~ ( v4_orders_2 @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r2_hidden @ sk_D_1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r1_waybel_0 @ sk_A @ sk_C_1 @ sk_B )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      & ( l1_waybel_0 @ sk_C_1 @ sk_A )
      & ( v3_yellow_6 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['170','184'])).

thf('186',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_D_1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( v4_orders_2 @ sk_C_1 ) )
   <= ( ( r1_waybel_0 @ sk_A @ sk_C_1 @ sk_B )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      & ( l1_waybel_0 @ sk_C_1 @ sk_A )
      & ( v3_yellow_6 @ sk_C_1 @ sk_A )
      & ( v7_waybel_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['169','185'])).

thf('187',plain,
    ( ( ( v2_struct_0 @ sk_C_1 )
      | ( r2_hidden @ sk_D_1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r1_waybel_0 @ sk_A @ sk_C_1 @ sk_B )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      & ( l1_waybel_0 @ sk_C_1 @ sk_A )
      & ( v3_yellow_6 @ sk_C_1 @ sk_A )
      & ( v7_waybel_0 @ sk_C_1 )
      & ( v4_orders_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['168','186'])).

thf('188',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( ( r2_hidden @ sk_D_1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ( r1_waybel_0 @ sk_A @ sk_C_1 @ sk_B )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      & ( l1_waybel_0 @ sk_C_1 @ sk_A )
      & ( v3_yellow_6 @ sk_C_1 @ sk_A )
      & ( v7_waybel_0 @ sk_C_1 )
      & ( v4_orders_2 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( ( r2_hidden @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ( v4_pre_topc @ sk_B @ sk_A )
      & ( r1_waybel_0 @ sk_A @ sk_C_1 @ sk_B )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      & ( l1_waybel_0 @ sk_C_1 @ sk_A )
      & ( v3_yellow_6 @ sk_C_1 @ sk_A )
      & ( v7_waybel_0 @ sk_C_1 )
      & ( v4_orders_2 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['167','189'])).

thf('191',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ sk_B )
   <= ~ ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['147'])).

thf('192',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r2_hidden @ sk_D_1 @ sk_B )
      & ( v4_pre_topc @ sk_B @ sk_A )
      & ( r1_waybel_0 @ sk_A @ sk_C_1 @ sk_B )
      & ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
      & ( l1_waybel_0 @ sk_C_1 @ sk_A )
      & ( v3_yellow_6 @ sk_C_1 @ sk_A )
      & ( v7_waybel_0 @ sk_C_1 )
      & ( v4_orders_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ~ ( v2_struct_0 @ sk_C_1 )
   <= ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(split,[status(esa)],['159'])).

thf('194',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( v3_yellow_6 @ sk_C_1 @ sk_A )
    | ~ ( v7_waybel_0 @ sk_C_1 )
    | ~ ( v4_orders_2 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_D_1 @ ( k10_yellow_6 @ sk_A @ sk_C_1 ) )
    | ~ ( l1_waybel_0 @ sk_C_1 @ sk_A )
    | ~ ( r1_waybel_0 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_D_1 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','143','144','146','148','150','152','154','156','158','160','194'])).


%------------------------------------------------------------------------------
