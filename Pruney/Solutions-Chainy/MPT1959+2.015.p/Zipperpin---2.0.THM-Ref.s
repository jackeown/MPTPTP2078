%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fgx1HBR7GP

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 226 expanded)
%              Number of leaves         :   31 (  77 expanded)
%              Depth                    :   16
%              Number of atoms          :  948 (3150 expanded)
%              Number of equality atoms :   25 (  47 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

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
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( X8 = X6 )
      | ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( r1_orders_2 @ X19 @ ( k3_yellow_0 @ X19 ) @ X18 )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v1_yellow_0 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('19',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('28',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('32',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v13_waybel_0 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( r2_hidden @ X22 @ X20 )
      | ~ ( r1_orders_2 @ X21 @ X23 @ X22 )
      | ~ ( r2_hidden @ X23 @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( X8 = X6 )
      | ~ ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('47',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['40','47'])).

thf('49',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('50',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['50','52'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('54',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_subset_1 @ X25 @ X24 )
      | ( X25 != X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('55',plain,(
    ! [X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( v1_subset_1 @ X24 @ X24 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('57',plain,(
    ! [X24: $i] :
      ~ ( v1_subset_1 @ X24 @ X24 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['51'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( v1_subset_1 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('62',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('65',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('70',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['51'])).

thf('75',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','58','59','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fgx1HBR7GP
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:03:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 151 iterations in 0.061s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.51  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.21/0.51  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.51  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.51  thf(t8_waybel_7, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.21/0.51         ( l1_orders_2 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.21/0.51             ( v13_waybel_0 @ B @ A ) & 
% 0.21/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.51           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.21/0.51             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.51            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.21/0.51            ( l1_orders_2 @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.21/0.51                ( v13_waybel_0 @ B @ A ) & 
% 0.21/0.51                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.51              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.21/0.51                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.21/0.51        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.21/0.51       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d10_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.51  thf(t3_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X11 : $i, X13 : $i]:
% 0.21/0.51         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('6', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(t8_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51           ( ( ![D:$i]:
% 0.21/0.51               ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.51                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.21/0.51             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.21/0.52          | ((X8) = (X6))
% 0.21/0.52          | (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X8)
% 0.21/0.52          | (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X6)
% 0.21/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.21/0.52          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.21/0.52          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.21/0.52          | ((X1) = (X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.21/0.52        | (r2_hidden @ 
% 0.21/0.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.21/0.52        | (r2_hidden @ 
% 0.21/0.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.52           (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(l3_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.52          | (r2_hidden @ X3 @ X5)
% 0.21/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (((r2_hidden @ 
% 0.21/0.52         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.52         (u1_struct_0 @ sk_A))
% 0.21/0.52        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['9', '12'])).
% 0.21/0.52  thf('14', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf(t4_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X14 @ X15)
% 0.21/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.21/0.52          | (m1_subset_1 @ X14 @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.21/0.52        | (m1_subset_1 @ 
% 0.21/0.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.52           (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.52  thf(t44_yellow_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.21/0.52         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.21/0.52          | (r1_orders_2 @ X19 @ (k3_yellow_0 @ X19) @ X18)
% 0.21/0.52          | ~ (l1_orders_2 @ X19)
% 0.21/0.52          | ~ (v1_yellow_0 @ X19)
% 0.21/0.52          | ~ (v5_orders_2 @ X19)
% 0.21/0.52          | (v2_struct_0 @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.52        | ~ (v1_yellow_0 @ sk_A)
% 0.21/0.52        | ~ (l1_orders_2 @ sk_A)
% 0.21/0.52        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.21/0.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf('20', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('21', plain, ((v1_yellow_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.21/0.52        | (v2_struct_0 @ sk_A)
% 0.21/0.52        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.21/0.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.21/0.52  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.21/0.52         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.21/0.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.21/0.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.21/0.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d20_waybel_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_orders_2 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.21/0.52             ( ![C:$i]:
% 0.21/0.52               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52                 ( ![D:$i]:
% 0.21/0.52                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.21/0.52                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.52          | ~ (v13_waybel_0 @ X20 @ X21)
% 0.21/0.52          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.21/0.52          | (r2_hidden @ X22 @ X20)
% 0.21/0.52          | ~ (r1_orders_2 @ X21 @ X23 @ X22)
% 0.21/0.52          | ~ (r2_hidden @ X23 @ X20)
% 0.21/0.52          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.21/0.52          | ~ (l1_orders_2 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.52          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.21/0.52          | (r2_hidden @ X1 @ sk_B)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.52  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.52          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.21/0.52          | (r2_hidden @ X1 @ sk_B)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52           | (r2_hidden @ X0 @ sk_B)
% 0.21/0.52           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.21/0.52           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.21/0.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.21/0.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52           | (r2_hidden @ X0 @ sk_B)
% 0.21/0.52           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.21/0.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.21/0.52         | (r2_hidden @ 
% 0.21/0.52            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.21/0.52         | ~ (m1_subset_1 @ 
% 0.21/0.52              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.52              (u1_struct_0 @ sk_A))))
% 0.21/0.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['25', '39'])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('42', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.21/0.52          | ((X8) = (X6))
% 0.21/0.52          | ~ (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X8)
% 0.21/0.52          | ~ (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X6)
% 0.21/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.21/0.52          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.21/0.52          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.21/0.52          | ((X1) = (X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.21/0.52        | ~ (r2_hidden @ 
% 0.21/0.52             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.21/0.52        | ~ (r2_hidden @ 
% 0.21/0.52             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.52             (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['41', '44'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      ((~ (r2_hidden @ 
% 0.21/0.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.21/0.52        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (((~ (m1_subset_1 @ 
% 0.21/0.52            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.52            (u1_struct_0 @ sk_A))
% 0.21/0.52         | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.21/0.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.21/0.52      inference('clc', [status(thm)], ['40', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.21/0.52        | (m1_subset_1 @ 
% 0.21/0.52           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.52           (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.52         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.21/0.52      inference('clc', [status(thm)], ['48', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.21/0.52        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.21/0.52         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('split', [status(esa)], ['51'])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (((v1_subset_1 @ sk_B @ sk_B))
% 0.21/0.52         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.21/0.52             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['50', '52'])).
% 0.21/0.52  thf(d7_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         (~ (v1_subset_1 @ X25 @ X24)
% 0.21/0.52          | ((X25) != (X24))
% 0.21/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      (![X24 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X24))
% 0.21/0.52          | ~ (v1_subset_1 @ X24 @ X24))),
% 0.21/0.52      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.52  thf('56', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('57', plain, (![X24 : $i]: ~ (v1_subset_1 @ X24 @ X24)),
% 0.21/0.52      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.21/0.52       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['53', '57'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.21/0.52       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['51'])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         (((X25) = (X24))
% 0.21/0.52          | (v1_subset_1 @ X25 @ X24)
% 0.21/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.52  thf(dt_k3_yellow_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_orders_2 @ A ) =>
% 0.21/0.52       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (![X17 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (k3_yellow_0 @ X17) @ (u1_struct_0 @ X17))
% 0.21/0.52          | ~ (l1_orders_2 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.21/0.52  thf(t2_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         ((r2_hidden @ X9 @ X10)
% 0.21/0.52          | (v1_xboole_0 @ X10)
% 0.21/0.52          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_orders_2 @ X0)
% 0.21/0.52          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.21/0.52          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.21/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.52         | ~ (l1_orders_2 @ sk_A)))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['64', '67'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.52  thf('70', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B) | (v1_xboole_0 @ sk_B)))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.52  thf('72', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.21/0.52         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('clc', [status(thm)], ['71', '72'])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.21/0.52         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['51'])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.21/0.52       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.52  thf('76', plain, ($false),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['1', '58', '59', '75'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
