%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Iss5AVBrLK

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:15 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 269 expanded)
%              Number of leaves         :   33 (  91 expanded)
%              Depth                    :   18
%              Number of atoms          : 1097 (3491 expanded)
%              Number of equality atoms :   29 (  46 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t8_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ A )
            & ( v13_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
          <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_yellow_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v2_waybel_0 @ B @ A )
              & ( v13_waybel_0 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
            <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_waybel_7])).

thf('0',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ( X9
       != ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( m1_subset_1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( X17 = X15 )
      | ( m1_subset_1 @ ( sk_D @ X15 @ X17 @ X16 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( r1_orders_2 @ X23 @ ( k3_yellow_0 @ X23 ) @ X22 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v1_yellow_0 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('18',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( m1_subset_1 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d20_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v13_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ B )
                        & ( r1_orders_2 @ A @ C @ D ) )
                     => ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v13_waybel_0 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ( r2_hidden @ X26 @ X24 )
      | ~ ( r1_orders_2 @ X25 @ X27 @ X26 )
      | ~ ( r2_hidden @ X27 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','38'])).

thf('40',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('41',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( X17 = X15 )
      | ~ ( r2_hidden @ ( sk_D @ X15 @ X17 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ ( sk_D @ X15 @ X17 @ X16 ) @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('47',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('51',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('58',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r1_tarski @ X10 @ X8 )
      | ( X9
       != ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('63',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','66'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference(clc,[status(thm)],['51','71'])).

thf('73',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['48','72'])).

thf('74',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['74'])).

thf('76',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['73','75'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('77',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_subset_1 @ X29 @ X28 )
      | ( X29 != X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('78',plain,(
    ! [X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( v1_subset_1 @ X28 @ X28 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('80',plain,(
    ! [X28: $i] :
      ~ ( v1_subset_1 @ X28 @ X28 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','80'])).

thf('82',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['74'])).

thf('83',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X29 = X28 )
      | ( v1_subset_1 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('85',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('88',plain,(
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('89',plain,
    ( ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('93',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['74'])).

thf('97',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','81','82','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Iss5AVBrLK
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:38:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.34  % Running portfolio for 600 s
% 0.21/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.71/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.71/0.93  % Solved by: fo/fo7.sh
% 0.71/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.93  % done 765 iterations in 0.473s
% 0.71/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.71/0.93  % SZS output start Refutation
% 0.71/0.93  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.71/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.93  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.71/0.93  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.71/0.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.71/0.93  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.71/0.93  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.71/0.93  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.71/0.93  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.71/0.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.71/0.93  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.71/0.93  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.71/0.93  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.71/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.93  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.71/0.93  thf(sk_B_type, type, sk_B: $i > $i).
% 0.71/0.93  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.71/0.93  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.71/0.93  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.71/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.93  thf(t8_waybel_7, conjecture,
% 0.71/0.93    (![A:$i]:
% 0.71/0.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.71/0.93         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.71/0.93         ( l1_orders_2 @ A ) ) =>
% 0.71/0.93       ( ![B:$i]:
% 0.71/0.93         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.71/0.93             ( v13_waybel_0 @ B @ A ) & 
% 0.71/0.93             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.71/0.93           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.71/0.93             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.71/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.93    (~( ![A:$i]:
% 0.71/0.93        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.71/0.93            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.71/0.93            ( l1_orders_2 @ A ) ) =>
% 0.71/0.93          ( ![B:$i]:
% 0.71/0.93            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.71/0.93                ( v13_waybel_0 @ B @ A ) & 
% 0.71/0.93                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.71/0.93              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.71/0.93                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.71/0.93    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.71/0.93  thf('0', plain,
% 0.71/0.93      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.71/0.93        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('1', plain,
% 0.71/0.93      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.71/0.93       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('split', [status(esa)], ['0'])).
% 0.71/0.93  thf(d3_tarski, axiom,
% 0.71/0.93    (![A:$i,B:$i]:
% 0.71/0.93     ( ( r1_tarski @ A @ B ) <=>
% 0.71/0.93       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.71/0.93  thf('2', plain,
% 0.71/0.93      (![X4 : $i, X6 : $i]:
% 0.71/0.93         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.71/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.93  thf('3', plain,
% 0.71/0.93      (![X4 : $i, X6 : $i]:
% 0.71/0.93         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.71/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.93  thf('4', plain,
% 0.71/0.93      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.71/0.93      inference('sup-', [status(thm)], ['2', '3'])).
% 0.71/0.93  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.71/0.93      inference('simplify', [status(thm)], ['4'])).
% 0.71/0.93  thf(d1_zfmisc_1, axiom,
% 0.71/0.93    (![A:$i,B:$i]:
% 0.71/0.93     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.71/0.93       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.71/0.93  thf('6', plain,
% 0.71/0.93      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.71/0.93         (~ (r1_tarski @ X7 @ X8)
% 0.71/0.93          | (r2_hidden @ X7 @ X9)
% 0.71/0.93          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 0.71/0.93      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.71/0.93  thf('7', plain,
% 0.71/0.93      (![X7 : $i, X8 : $i]:
% 0.71/0.93         ((r2_hidden @ X7 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X7 @ X8))),
% 0.71/0.93      inference('simplify', [status(thm)], ['6'])).
% 0.71/0.93  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.71/0.93      inference('sup-', [status(thm)], ['5', '7'])).
% 0.71/0.93  thf(d2_subset_1, axiom,
% 0.71/0.93    (![A:$i,B:$i]:
% 0.71/0.93     ( ( ( v1_xboole_0 @ A ) =>
% 0.71/0.93         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.71/0.93       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.71/0.93         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.71/0.93  thf('9', plain,
% 0.71/0.93      (![X12 : $i, X13 : $i]:
% 0.71/0.93         (~ (r2_hidden @ X12 @ X13)
% 0.71/0.93          | (m1_subset_1 @ X12 @ X13)
% 0.71/0.93          | (v1_xboole_0 @ X13))),
% 0.71/0.93      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.71/0.93  thf(d1_xboole_0, axiom,
% 0.71/0.93    (![A:$i]:
% 0.71/0.93     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.71/0.93  thf('10', plain,
% 0.71/0.93      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.71/0.93      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.71/0.93  thf('11', plain,
% 0.71/0.93      (![X12 : $i, X13 : $i]:
% 0.71/0.93         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.71/0.93      inference('clc', [status(thm)], ['9', '10'])).
% 0.71/0.93  thf('12', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.71/0.93      inference('sup-', [status(thm)], ['8', '11'])).
% 0.71/0.93  thf('13', plain,
% 0.71/0.93      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf(t8_subset_1, axiom,
% 0.71/0.93    (![A:$i,B:$i]:
% 0.71/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.71/0.93       ( ![C:$i]:
% 0.71/0.93         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.71/0.93           ( ( ![D:$i]:
% 0.71/0.93               ( ( m1_subset_1 @ D @ A ) =>
% 0.71/0.93                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.71/0.93             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.71/0.93  thf('14', plain,
% 0.71/0.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.71/0.93         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.71/0.93          | ((X17) = (X15))
% 0.71/0.93          | (m1_subset_1 @ (sk_D @ X15 @ X17 @ X16) @ X16)
% 0.71/0.93          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.71/0.93      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.71/0.93  thf('15', plain,
% 0.71/0.93      (![X0 : $i]:
% 0.71/0.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.93          | (m1_subset_1 @ (sk_D @ sk_B_1 @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 0.71/0.93             (u1_struct_0 @ sk_A))
% 0.71/0.93          | ((X0) = (sk_B_1)))),
% 0.71/0.93      inference('sup-', [status(thm)], ['13', '14'])).
% 0.71/0.93  thf('16', plain,
% 0.71/0.93      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.71/0.93        | (m1_subset_1 @ 
% 0.71/0.93           (sk_D @ sk_B_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 0.71/0.93           (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('sup-', [status(thm)], ['12', '15'])).
% 0.71/0.93  thf(t44_yellow_0, axiom,
% 0.71/0.93    (![A:$i]:
% 0.71/0.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.71/0.93         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.71/0.93       ( ![B:$i]:
% 0.71/0.93         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.71/0.93           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.71/0.93  thf('17', plain,
% 0.71/0.93      (![X22 : $i, X23 : $i]:
% 0.71/0.93         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.71/0.93          | (r1_orders_2 @ X23 @ (k3_yellow_0 @ X23) @ X22)
% 0.71/0.93          | ~ (l1_orders_2 @ X23)
% 0.71/0.93          | ~ (v1_yellow_0 @ X23)
% 0.71/0.93          | ~ (v5_orders_2 @ X23)
% 0.71/0.93          | (v2_struct_0 @ X23))),
% 0.71/0.93      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.71/0.93  thf('18', plain,
% 0.71/0.93      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.71/0.93        | (v2_struct_0 @ sk_A)
% 0.71/0.93        | ~ (v5_orders_2 @ sk_A)
% 0.71/0.93        | ~ (v1_yellow_0 @ sk_A)
% 0.71/0.93        | ~ (l1_orders_2 @ sk_A)
% 0.71/0.93        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.71/0.93           (sk_D @ sk_B_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.71/0.93      inference('sup-', [status(thm)], ['16', '17'])).
% 0.71/0.93  thf('19', plain, ((v5_orders_2 @ sk_A)),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('20', plain, ((v1_yellow_0 @ sk_A)),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('22', plain,
% 0.71/0.93      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.71/0.93        | (v2_struct_0 @ sk_A)
% 0.71/0.93        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.71/0.93           (sk_D @ sk_B_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.71/0.93      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.71/0.93  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('24', plain,
% 0.71/0.93      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.71/0.93         (sk_D @ sk_B_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.71/0.93        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.71/0.93      inference('clc', [status(thm)], ['22', '23'])).
% 0.71/0.93  thf('25', plain,
% 0.71/0.93      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.71/0.93         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.71/0.93      inference('split', [status(esa)], ['0'])).
% 0.71/0.93  thf('26', plain,
% 0.71/0.93      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf(t4_subset, axiom,
% 0.71/0.93    (![A:$i,B:$i,C:$i]:
% 0.71/0.93     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.71/0.93       ( m1_subset_1 @ A @ C ) ))).
% 0.71/0.93  thf('27', plain,
% 0.71/0.93      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.71/0.93         (~ (r2_hidden @ X18 @ X19)
% 0.71/0.93          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.71/0.93          | (m1_subset_1 @ X18 @ X20))),
% 0.71/0.93      inference('cnf', [status(esa)], [t4_subset])).
% 0.71/0.93  thf('28', plain,
% 0.71/0.93      (![X0 : $i]:
% 0.71/0.93         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.71/0.93          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.71/0.93      inference('sup-', [status(thm)], ['26', '27'])).
% 0.71/0.93  thf('29', plain,
% 0.71/0.93      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.71/0.93         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.71/0.93      inference('sup-', [status(thm)], ['25', '28'])).
% 0.71/0.93  thf('30', plain,
% 0.71/0.93      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf(d20_waybel_0, axiom,
% 0.71/0.93    (![A:$i]:
% 0.71/0.93     ( ( l1_orders_2 @ A ) =>
% 0.71/0.93       ( ![B:$i]:
% 0.71/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.93           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.71/0.93             ( ![C:$i]:
% 0.71/0.93               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.71/0.93                 ( ![D:$i]:
% 0.71/0.93                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.71/0.93                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.71/0.93                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.71/0.93  thf('31', plain,
% 0.71/0.93      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.71/0.93         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.71/0.93          | ~ (v13_waybel_0 @ X24 @ X25)
% 0.71/0.93          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.71/0.93          | (r2_hidden @ X26 @ X24)
% 0.71/0.93          | ~ (r1_orders_2 @ X25 @ X27 @ X26)
% 0.71/0.93          | ~ (r2_hidden @ X27 @ X24)
% 0.71/0.93          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.71/0.93          | ~ (l1_orders_2 @ X25))),
% 0.71/0.93      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.71/0.93  thf('32', plain,
% 0.71/0.93      (![X0 : $i, X1 : $i]:
% 0.71/0.93         (~ (l1_orders_2 @ sk_A)
% 0.71/0.93          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.71/0.93          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.71/0.93          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.71/0.93          | (r2_hidden @ X1 @ sk_B_1)
% 0.71/0.93          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.71/0.93          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 0.71/0.93      inference('sup-', [status(thm)], ['30', '31'])).
% 0.71/0.93  thf('33', plain, ((l1_orders_2 @ sk_A)),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('34', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('35', plain,
% 0.71/0.93      (![X0 : $i, X1 : $i]:
% 0.71/0.93         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.71/0.93          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.71/0.93          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.71/0.93          | (r2_hidden @ X1 @ sk_B_1)
% 0.71/0.93          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.71/0.93  thf('36', plain,
% 0.71/0.93      ((![X0 : $i]:
% 0.71/0.93          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.71/0.93           | (r2_hidden @ X0 @ sk_B_1)
% 0.71/0.93           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.71/0.93           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.71/0.93         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.71/0.93      inference('sup-', [status(thm)], ['29', '35'])).
% 0.71/0.93  thf('37', plain,
% 0.71/0.93      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.71/0.93         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.71/0.93      inference('split', [status(esa)], ['0'])).
% 0.71/0.93  thf('38', plain,
% 0.71/0.93      ((![X0 : $i]:
% 0.71/0.93          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.71/0.93           | (r2_hidden @ X0 @ sk_B_1)
% 0.71/0.93           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.71/0.93         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.71/0.93      inference('demod', [status(thm)], ['36', '37'])).
% 0.71/0.93  thf('39', plain,
% 0.71/0.93      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.71/0.93         | (r2_hidden @ 
% 0.71/0.93            (sk_D @ sk_B_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 0.71/0.93            sk_B_1)
% 0.71/0.93         | ~ (m1_subset_1 @ 
% 0.71/0.93              (sk_D @ sk_B_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 0.71/0.93              (u1_struct_0 @ sk_A))))
% 0.71/0.93         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.71/0.93      inference('sup-', [status(thm)], ['24', '38'])).
% 0.71/0.93  thf('40', plain,
% 0.71/0.93      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.71/0.93        | (m1_subset_1 @ 
% 0.71/0.93           (sk_D @ sk_B_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 0.71/0.93           (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('sup-', [status(thm)], ['12', '15'])).
% 0.71/0.93  thf('41', plain,
% 0.71/0.93      ((((r2_hidden @ 
% 0.71/0.93          (sk_D @ sk_B_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 0.71/0.93          sk_B_1)
% 0.71/0.93         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.71/0.93         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.71/0.93      inference('clc', [status(thm)], ['39', '40'])).
% 0.71/0.93  thf('42', plain,
% 0.71/0.93      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('43', plain,
% 0.71/0.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.71/0.93         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.71/0.93          | ((X17) = (X15))
% 0.71/0.93          | ~ (r2_hidden @ (sk_D @ X15 @ X17 @ X16) @ X17)
% 0.71/0.93          | ~ (r2_hidden @ (sk_D @ X15 @ X17 @ X16) @ X15)
% 0.71/0.93          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.71/0.93      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.71/0.93  thf('44', plain,
% 0.71/0.93      (![X0 : $i]:
% 0.71/0.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.93          | ~ (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 0.71/0.93          | ~ (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.71/0.93          | ((X0) = (sk_B_1)))),
% 0.71/0.93      inference('sup-', [status(thm)], ['42', '43'])).
% 0.71/0.93  thf('45', plain,
% 0.71/0.93      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.71/0.93         | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.71/0.93         | ~ (r2_hidden @ 
% 0.71/0.93              (sk_D @ sk_B_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 0.71/0.93              (u1_struct_0 @ sk_A))
% 0.71/0.93         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.71/0.93              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.71/0.93         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.71/0.93      inference('sup-', [status(thm)], ['41', '44'])).
% 0.71/0.93  thf('46', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.71/0.93      inference('sup-', [status(thm)], ['8', '11'])).
% 0.71/0.93  thf('47', plain,
% 0.71/0.93      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.71/0.93         | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.71/0.93         | ~ (r2_hidden @ 
% 0.71/0.93              (sk_D @ sk_B_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 0.71/0.93              (u1_struct_0 @ sk_A))))
% 0.71/0.93         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.71/0.93      inference('demod', [status(thm)], ['45', '46'])).
% 0.71/0.93  thf('48', plain,
% 0.71/0.93      (((~ (r2_hidden @ 
% 0.71/0.93            (sk_D @ sk_B_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 0.71/0.93            (u1_struct_0 @ sk_A))
% 0.71/0.93         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.71/0.93         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.71/0.93      inference('simplify', [status(thm)], ['47'])).
% 0.71/0.93  thf('49', plain,
% 0.71/0.93      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.71/0.93        | (m1_subset_1 @ 
% 0.71/0.93           (sk_D @ sk_B_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 0.71/0.93           (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('sup-', [status(thm)], ['12', '15'])).
% 0.71/0.93  thf('50', plain,
% 0.71/0.93      (![X12 : $i, X13 : $i]:
% 0.71/0.93         (~ (m1_subset_1 @ X12 @ X13)
% 0.71/0.93          | (r2_hidden @ X12 @ X13)
% 0.71/0.93          | (v1_xboole_0 @ X13))),
% 0.71/0.93      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.71/0.93  thf('51', plain,
% 0.71/0.93      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.71/0.93        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.93        | (r2_hidden @ 
% 0.71/0.93           (sk_D @ sk_B_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 0.71/0.93           (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('sup-', [status(thm)], ['49', '50'])).
% 0.71/0.93  thf('52', plain,
% 0.71/0.93      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.71/0.93      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.71/0.93  thf('53', plain,
% 0.71/0.93      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('54', plain,
% 0.71/0.93      (![X12 : $i, X13 : $i]:
% 0.71/0.93         (~ (m1_subset_1 @ X12 @ X13)
% 0.71/0.93          | (r2_hidden @ X12 @ X13)
% 0.71/0.93          | (v1_xboole_0 @ X13))),
% 0.71/0.93      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.71/0.93  thf('55', plain,
% 0.71/0.93      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.93        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.71/0.93      inference('sup-', [status(thm)], ['53', '54'])).
% 0.71/0.93  thf('56', plain,
% 0.71/0.93      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('57', plain,
% 0.71/0.93      (![X13 : $i, X14 : $i]:
% 0.71/0.93         (~ (m1_subset_1 @ X14 @ X13)
% 0.71/0.93          | (v1_xboole_0 @ X14)
% 0.71/0.93          | ~ (v1_xboole_0 @ X13))),
% 0.71/0.93      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.71/0.93  thf('58', plain,
% 0.71/0.93      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.93        | (v1_xboole_0 @ sk_B_1))),
% 0.71/0.93      inference('sup-', [status(thm)], ['56', '57'])).
% 0.71/0.93  thf('59', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('60', plain, (~ (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('clc', [status(thm)], ['58', '59'])).
% 0.71/0.93  thf('61', plain,
% 0.71/0.93      ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('clc', [status(thm)], ['55', '60'])).
% 0.71/0.93  thf('62', plain,
% 0.71/0.93      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.71/0.93         (~ (r2_hidden @ X10 @ X9)
% 0.71/0.93          | (r1_tarski @ X10 @ X8)
% 0.71/0.93          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 0.71/0.93      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.71/0.93  thf('63', plain,
% 0.71/0.93      (![X8 : $i, X10 : $i]:
% 0.71/0.93         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.71/0.93      inference('simplify', [status(thm)], ['62'])).
% 0.71/0.93  thf('64', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.71/0.93      inference('sup-', [status(thm)], ['61', '63'])).
% 0.71/0.93  thf('65', plain,
% 0.71/0.93      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.71/0.93         (~ (r2_hidden @ X3 @ X4)
% 0.71/0.93          | (r2_hidden @ X3 @ X5)
% 0.71/0.93          | ~ (r1_tarski @ X4 @ X5))),
% 0.71/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.71/0.93  thf('66', plain,
% 0.71/0.93      (![X0 : $i]:
% 0.71/0.93         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.71/0.93      inference('sup-', [status(thm)], ['64', '65'])).
% 0.71/0.93  thf('67', plain,
% 0.71/0.93      (((v1_xboole_0 @ sk_B_1)
% 0.71/0.93        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('sup-', [status(thm)], ['52', '66'])).
% 0.71/0.93  thf('68', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('69', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.71/0.93      inference('clc', [status(thm)], ['67', '68'])).
% 0.71/0.93  thf('70', plain,
% 0.71/0.93      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.71/0.93      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.71/0.93  thf('71', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.71/0.93      inference('sup-', [status(thm)], ['69', '70'])).
% 0.71/0.93  thf('72', plain,
% 0.71/0.93      (((r2_hidden @ 
% 0.71/0.93         (sk_D @ sk_B_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 0.71/0.93         (u1_struct_0 @ sk_A))
% 0.71/0.93        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.71/0.93      inference('clc', [status(thm)], ['51', '71'])).
% 0.71/0.93  thf('73', plain,
% 0.71/0.93      ((((u1_struct_0 @ sk_A) = (sk_B_1)))
% 0.71/0.93         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.71/0.93      inference('clc', [status(thm)], ['48', '72'])).
% 0.71/0.93  thf('74', plain,
% 0.71/0.93      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.71/0.93        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('75', plain,
% 0.71/0.93      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.93         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.71/0.93      inference('split', [status(esa)], ['74'])).
% 0.71/0.93  thf('76', plain,
% 0.71/0.93      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.71/0.93         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 0.71/0.93             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.71/0.93      inference('sup+', [status(thm)], ['73', '75'])).
% 0.71/0.93  thf(d7_subset_1, axiom,
% 0.71/0.93    (![A:$i,B:$i]:
% 0.71/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.71/0.93       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.71/0.93  thf('77', plain,
% 0.71/0.93      (![X28 : $i, X29 : $i]:
% 0.71/0.93         (~ (v1_subset_1 @ X29 @ X28)
% 0.71/0.93          | ((X29) != (X28))
% 0.71/0.93          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.71/0.93      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.71/0.93  thf('78', plain,
% 0.71/0.93      (![X28 : $i]:
% 0.71/0.93         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X28))
% 0.71/0.93          | ~ (v1_subset_1 @ X28 @ X28))),
% 0.71/0.93      inference('simplify', [status(thm)], ['77'])).
% 0.71/0.93  thf('79', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.71/0.93      inference('sup-', [status(thm)], ['8', '11'])).
% 0.71/0.93  thf('80', plain, (![X28 : $i]: ~ (v1_subset_1 @ X28 @ X28)),
% 0.71/0.93      inference('demod', [status(thm)], ['78', '79'])).
% 0.71/0.93  thf('81', plain,
% 0.71/0.93      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.71/0.93       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('sup-', [status(thm)], ['76', '80'])).
% 0.71/0.93  thf('82', plain,
% 0.71/0.93      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.71/0.93       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('split', [status(esa)], ['74'])).
% 0.71/0.93  thf('83', plain,
% 0.71/0.93      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('84', plain,
% 0.71/0.93      (![X28 : $i, X29 : $i]:
% 0.71/0.93         (((X29) = (X28))
% 0.71/0.93          | (v1_subset_1 @ X29 @ X28)
% 0.71/0.93          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.71/0.93      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.71/0.93  thf('85', plain,
% 0.71/0.93      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.71/0.93        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('sup-', [status(thm)], ['83', '84'])).
% 0.71/0.93  thf('86', plain,
% 0.71/0.93      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.93         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.71/0.93      inference('split', [status(esa)], ['0'])).
% 0.71/0.93  thf('87', plain,
% 0.71/0.93      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.71/0.93         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.71/0.93      inference('sup-', [status(thm)], ['85', '86'])).
% 0.71/0.93  thf(dt_k3_yellow_0, axiom,
% 0.71/0.93    (![A:$i]:
% 0.71/0.93     ( ( l1_orders_2 @ A ) =>
% 0.71/0.93       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.71/0.93  thf('88', plain,
% 0.71/0.93      (![X21 : $i]:
% 0.71/0.93         ((m1_subset_1 @ (k3_yellow_0 @ X21) @ (u1_struct_0 @ X21))
% 0.71/0.93          | ~ (l1_orders_2 @ X21))),
% 0.71/0.93      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.71/0.93  thf('89', plain,
% 0.71/0.93      ((((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_1) | ~ (l1_orders_2 @ sk_A)))
% 0.71/0.93         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.71/0.93      inference('sup+', [status(thm)], ['87', '88'])).
% 0.71/0.93  thf('90', plain, ((l1_orders_2 @ sk_A)),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('91', plain,
% 0.71/0.93      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.71/0.93         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.71/0.93      inference('demod', [status(thm)], ['89', '90'])).
% 0.71/0.93  thf('92', plain,
% 0.71/0.93      (![X12 : $i, X13 : $i]:
% 0.71/0.93         (~ (m1_subset_1 @ X12 @ X13)
% 0.71/0.93          | (r2_hidden @ X12 @ X13)
% 0.71/0.93          | (v1_xboole_0 @ X13))),
% 0.71/0.93      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.71/0.93  thf('93', plain,
% 0.71/0.93      ((((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.71/0.93         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.71/0.93      inference('sup-', [status(thm)], ['91', '92'])).
% 0.71/0.93  thf('94', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.71/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.93  thf('95', plain,
% 0.71/0.93      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.71/0.93         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.71/0.93      inference('clc', [status(thm)], ['93', '94'])).
% 0.71/0.93  thf('96', plain,
% 0.71/0.93      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.71/0.93         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.71/0.93      inference('split', [status(esa)], ['74'])).
% 0.71/0.93  thf('97', plain,
% 0.71/0.93      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.71/0.93       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.93      inference('sup-', [status(thm)], ['95', '96'])).
% 0.71/0.93  thf('98', plain, ($false),
% 0.71/0.93      inference('sat_resolution*', [status(thm)], ['1', '81', '82', '97'])).
% 0.71/0.93  
% 0.71/0.93  % SZS output end Refutation
% 0.71/0.93  
% 0.77/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
