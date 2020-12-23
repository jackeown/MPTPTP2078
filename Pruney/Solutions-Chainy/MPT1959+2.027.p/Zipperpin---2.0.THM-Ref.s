%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tNxLpAFhTP

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:12 EST 2020

% Result     : Theorem 3.51s
% Output     : Refutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 256 expanded)
%              Number of leaves         :   41 (  90 expanded)
%              Depth                    :   25
%              Number of atoms          : 1212 (3937 expanded)
%              Number of equality atoms :   47 (  64 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

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

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X15: $i] :
      ( ( ( k3_yellow_0 @ X15 )
        = ( k1_yellow_0 @ X15 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 )
      | ( sk_B = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('10',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t34_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) )
            & ( ( k1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) )
              = B ) ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( ( k1_yellow_0 @ X26 @ ( k5_waybel_0 @ X26 @ X25 ) )
        = X25 )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v3_orders_2 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('12',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(t42_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( r1_yellow_0 @ A @ k1_xboole_0 )
        & ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X20: $i] :
      ( ( r1_yellow_0 @ X20 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v1_yellow_0 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( r1_yellow_0 @ X26 @ ( k5_waybel_0 @ X26 @ X25 ) )
      | ~ ( l1_orders_2 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v3_orders_2 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('24',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(t34_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( ( r1_tarski @ B @ C )
            & ( r1_yellow_0 @ A @ B )
            & ( r1_yellow_0 @ A @ C ) )
         => ( r1_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_orders_2 @ X17 @ ( k1_yellow_0 @ X17 @ X18 ) @ ( k1_yellow_0 @ X17 @ X19 ) )
      | ~ ( r1_yellow_0 @ X17 @ X19 )
      | ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_yellow_0 @ X17 @ X18 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t34_yellow_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['20','36'])).

thf('38',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','43'])).

thf('45',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','45'])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('51',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v13_waybel_0 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ( r2_hidden @ X23 @ X21 )
      | ~ ( r1_orders_2 @ X22 @ X24 @ X23 )
      | ~ ( r2_hidden @ X24 @ X21 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['48','62'])).

thf('64',plain,
    ( ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('66',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['63','67'])).

thf('69',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('70',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['70','72'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('74',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_subset_1 @ X28 @ X27 )
      | ( X28 != X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('75',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( v1_subset_1 @ X27 @ X27 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('76',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('77',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('78',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X27: $i] :
      ~ ( v1_subset_1 @ X27 @ X27 ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('80',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['71'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X28 = X27 )
      | ( v1_subset_1 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('84',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('87',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('88',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('92',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['71'])).

thf('97',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','80','81','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tNxLpAFhTP
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.51/3.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.51/3.75  % Solved by: fo/fo7.sh
% 3.51/3.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.51/3.75  % done 1053 iterations in 3.301s
% 3.51/3.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.51/3.75  % SZS output start Refutation
% 3.51/3.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.51/3.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.51/3.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.51/3.75  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 3.51/3.75  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 3.51/3.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.51/3.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.51/3.75  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 3.51/3.75  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 3.51/3.75  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 3.51/3.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.51/3.75  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 3.51/3.75  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 3.51/3.75  thf(sk_B_type, type, sk_B: $i).
% 3.51/3.75  thf(sk_A_type, type, sk_A: $i).
% 3.51/3.75  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 3.51/3.75  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.51/3.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.51/3.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.51/3.75  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 3.51/3.75  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 3.51/3.75  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 3.51/3.75  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 3.51/3.75  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 3.51/3.75  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 3.51/3.75  thf(k5_waybel_0_type, type, k5_waybel_0: $i > $i > $i).
% 3.51/3.75  thf(t8_waybel_7, conjecture,
% 3.51/3.75    (![A:$i]:
% 3.51/3.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.51/3.75         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 3.51/3.75         ( l1_orders_2 @ A ) ) =>
% 3.51/3.75       ( ![B:$i]:
% 3.51/3.75         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 3.51/3.75             ( v13_waybel_0 @ B @ A ) & 
% 3.51/3.75             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.51/3.75           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 3.51/3.75             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 3.51/3.75  thf(zf_stmt_0, negated_conjecture,
% 3.51/3.75    (~( ![A:$i]:
% 3.51/3.75        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.51/3.75            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 3.51/3.75            ( l1_orders_2 @ A ) ) =>
% 3.51/3.75          ( ![B:$i]:
% 3.51/3.75            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 3.51/3.75                ( v13_waybel_0 @ B @ A ) & 
% 3.51/3.75                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.51/3.75              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 3.51/3.75                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 3.51/3.75    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 3.51/3.75  thf('0', plain,
% 3.51/3.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 3.51/3.75        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('1', plain,
% 3.51/3.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 3.51/3.75       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('split', [status(esa)], ['0'])).
% 3.51/3.75  thf(d11_yellow_0, axiom,
% 3.51/3.75    (![A:$i]:
% 3.51/3.75     ( ( l1_orders_2 @ A ) =>
% 3.51/3.75       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 3.51/3.75  thf('2', plain,
% 3.51/3.75      (![X15 : $i]:
% 3.51/3.75         (((k3_yellow_0 @ X15) = (k1_yellow_0 @ X15 @ k1_xboole_0))
% 3.51/3.75          | ~ (l1_orders_2 @ X15))),
% 3.51/3.75      inference('cnf', [status(esa)], [d11_yellow_0])).
% 3.51/3.75  thf(t2_tarski, axiom,
% 3.51/3.75    (![A:$i,B:$i]:
% 3.51/3.75     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 3.51/3.75       ( ( A ) = ( B ) ) ))).
% 3.51/3.75  thf('3', plain,
% 3.51/3.75      (![X0 : $i, X1 : $i]:
% 3.51/3.75         (((X1) = (X0))
% 3.51/3.75          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 3.51/3.75          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 3.51/3.75      inference('cnf', [status(esa)], [t2_tarski])).
% 3.51/3.75  thf('4', plain,
% 3.51/3.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf(l3_subset_1, axiom,
% 3.51/3.75    (![A:$i,B:$i]:
% 3.51/3.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.51/3.75       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 3.51/3.75  thf('5', plain,
% 3.51/3.75      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.51/3.75         (~ (r2_hidden @ X5 @ X6)
% 3.51/3.75          | (r2_hidden @ X5 @ X7)
% 3.51/3.75          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 3.51/3.75      inference('cnf', [status(esa)], [l3_subset_1])).
% 3.51/3.75  thf('6', plain,
% 3.51/3.75      (![X0 : $i]:
% 3.51/3.75         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 3.51/3.75      inference('sup-', [status(thm)], ['4', '5'])).
% 3.51/3.75  thf('7', plain,
% 3.51/3.75      (![X0 : $i]:
% 3.51/3.75         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ X0)
% 3.51/3.75          | ((sk_B) = (X0))
% 3.51/3.75          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('sup-', [status(thm)], ['3', '6'])).
% 3.51/3.75  thf('8', plain,
% 3.51/3.75      (((r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.51/3.75         (u1_struct_0 @ sk_A))
% 3.51/3.75        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('eq_fact', [status(thm)], ['7'])).
% 3.51/3.75  thf(t1_subset, axiom,
% 3.51/3.75    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 3.51/3.75  thf('9', plain,
% 3.51/3.75      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 3.51/3.75      inference('cnf', [status(esa)], [t1_subset])).
% 3.51/3.75  thf('10', plain,
% 3.51/3.75      ((((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75        | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.51/3.75           (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('sup-', [status(thm)], ['8', '9'])).
% 3.51/3.75  thf(t34_waybel_0, axiom,
% 3.51/3.75    (![A:$i]:
% 3.51/3.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.51/3.75         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 3.51/3.75       ( ![B:$i]:
% 3.51/3.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.51/3.75           ( ( r1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) ) & 
% 3.51/3.75             ( ( k1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 3.51/3.75  thf('11', plain,
% 3.51/3.75      (![X25 : $i, X26 : $i]:
% 3.51/3.75         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 3.51/3.75          | ((k1_yellow_0 @ X26 @ (k5_waybel_0 @ X26 @ X25)) = (X25))
% 3.51/3.75          | ~ (l1_orders_2 @ X26)
% 3.51/3.75          | ~ (v5_orders_2 @ X26)
% 3.51/3.75          | ~ (v4_orders_2 @ X26)
% 3.51/3.75          | ~ (v3_orders_2 @ X26)
% 3.51/3.75          | (v2_struct_0 @ X26))),
% 3.51/3.75      inference('cnf', [status(esa)], [t34_waybel_0])).
% 3.51/3.75  thf('12', plain,
% 3.51/3.75      ((((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75        | (v2_struct_0 @ sk_A)
% 3.51/3.75        | ~ (v3_orders_2 @ sk_A)
% 3.51/3.75        | ~ (v4_orders_2 @ sk_A)
% 3.51/3.75        | ~ (v5_orders_2 @ sk_A)
% 3.51/3.75        | ~ (l1_orders_2 @ sk_A)
% 3.51/3.75        | ((k1_yellow_0 @ sk_A @ 
% 3.51/3.75            (k5_waybel_0 @ sk_A @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))
% 3.51/3.75            = (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 3.51/3.75      inference('sup-', [status(thm)], ['10', '11'])).
% 3.51/3.75  thf('13', plain, ((v3_orders_2 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('14', plain, ((v4_orders_2 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('15', plain, ((v5_orders_2 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('17', plain,
% 3.51/3.75      ((((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75        | (v2_struct_0 @ sk_A)
% 3.51/3.75        | ((k1_yellow_0 @ sk_A @ 
% 3.51/3.75            (k5_waybel_0 @ sk_A @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))
% 3.51/3.75            = (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 3.51/3.75      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 3.51/3.75  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('19', plain,
% 3.51/3.75      ((((k1_yellow_0 @ sk_A @ 
% 3.51/3.75          (k5_waybel_0 @ sk_A @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))
% 3.51/3.75          = (sk_C @ (u1_struct_0 @ sk_A) @ sk_B))
% 3.51/3.75        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('clc', [status(thm)], ['17', '18'])).
% 3.51/3.75  thf(t42_yellow_0, axiom,
% 3.51/3.75    (![A:$i]:
% 3.51/3.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 3.51/3.75         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 3.51/3.75       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 3.51/3.75         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 3.51/3.75  thf('20', plain,
% 3.51/3.75      (![X20 : $i]:
% 3.51/3.75         ((r1_yellow_0 @ X20 @ k1_xboole_0)
% 3.51/3.75          | ~ (l1_orders_2 @ X20)
% 3.51/3.75          | ~ (v1_yellow_0 @ X20)
% 3.51/3.75          | ~ (v5_orders_2 @ X20)
% 3.51/3.75          | (v2_struct_0 @ X20))),
% 3.51/3.75      inference('cnf', [status(esa)], [t42_yellow_0])).
% 3.51/3.75  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.51/3.75  thf('21', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 3.51/3.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.51/3.75  thf('22', plain,
% 3.51/3.75      ((((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75        | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.51/3.75           (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('sup-', [status(thm)], ['8', '9'])).
% 3.51/3.75  thf('23', plain,
% 3.51/3.75      (![X25 : $i, X26 : $i]:
% 3.51/3.75         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 3.51/3.75          | (r1_yellow_0 @ X26 @ (k5_waybel_0 @ X26 @ X25))
% 3.51/3.75          | ~ (l1_orders_2 @ X26)
% 3.51/3.75          | ~ (v5_orders_2 @ X26)
% 3.51/3.75          | ~ (v4_orders_2 @ X26)
% 3.51/3.75          | ~ (v3_orders_2 @ X26)
% 3.51/3.75          | (v2_struct_0 @ X26))),
% 3.51/3.75      inference('cnf', [status(esa)], [t34_waybel_0])).
% 3.51/3.75  thf('24', plain,
% 3.51/3.75      ((((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75        | (v2_struct_0 @ sk_A)
% 3.51/3.75        | ~ (v3_orders_2 @ sk_A)
% 3.51/3.75        | ~ (v4_orders_2 @ sk_A)
% 3.51/3.75        | ~ (v5_orders_2 @ sk_A)
% 3.51/3.75        | ~ (l1_orders_2 @ sk_A)
% 3.51/3.75        | (r1_yellow_0 @ sk_A @ 
% 3.51/3.75           (k5_waybel_0 @ sk_A @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 3.51/3.75      inference('sup-', [status(thm)], ['22', '23'])).
% 3.51/3.75  thf('25', plain, ((v3_orders_2 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('26', plain, ((v4_orders_2 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('27', plain, ((v5_orders_2 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('29', plain,
% 3.51/3.75      ((((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75        | (v2_struct_0 @ sk_A)
% 3.51/3.75        | (r1_yellow_0 @ sk_A @ 
% 3.51/3.75           (k5_waybel_0 @ sk_A @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 3.51/3.75      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 3.51/3.75  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('31', plain,
% 3.51/3.75      (((r1_yellow_0 @ sk_A @ 
% 3.51/3.75         (k5_waybel_0 @ sk_A @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))
% 3.51/3.75        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('clc', [status(thm)], ['29', '30'])).
% 3.51/3.75  thf(t34_yellow_0, axiom,
% 3.51/3.75    (![A:$i]:
% 3.51/3.75     ( ( l1_orders_2 @ A ) =>
% 3.51/3.75       ( ![B:$i,C:$i]:
% 3.51/3.75         ( ( ( r1_tarski @ B @ C ) & ( r1_yellow_0 @ A @ B ) & 
% 3.51/3.75             ( r1_yellow_0 @ A @ C ) ) =>
% 3.51/3.75           ( r1_orders_2 @
% 3.51/3.75             A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) ))).
% 3.51/3.75  thf('32', plain,
% 3.51/3.75      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.51/3.75         ((r1_orders_2 @ X17 @ (k1_yellow_0 @ X17 @ X18) @ 
% 3.51/3.75           (k1_yellow_0 @ X17 @ X19))
% 3.51/3.75          | ~ (r1_yellow_0 @ X17 @ X19)
% 3.51/3.75          | ~ (r1_tarski @ X18 @ X19)
% 3.51/3.75          | ~ (r1_yellow_0 @ X17 @ X18)
% 3.51/3.75          | ~ (l1_orders_2 @ X17))),
% 3.51/3.75      inference('cnf', [status(esa)], [t34_yellow_0])).
% 3.51/3.75  thf('33', plain,
% 3.51/3.75      (![X0 : $i]:
% 3.51/3.75         (((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75          | ~ (l1_orders_2 @ sk_A)
% 3.51/3.75          | ~ (r1_yellow_0 @ sk_A @ X0)
% 3.51/3.75          | ~ (r1_tarski @ X0 @ 
% 3.51/3.75               (k5_waybel_0 @ sk_A @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))
% 3.51/3.75          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 3.51/3.75             (k1_yellow_0 @ sk_A @ 
% 3.51/3.75              (k5_waybel_0 @ sk_A @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 3.51/3.75      inference('sup-', [status(thm)], ['31', '32'])).
% 3.51/3.75  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('35', plain,
% 3.51/3.75      (![X0 : $i]:
% 3.51/3.75         (((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75          | ~ (r1_yellow_0 @ sk_A @ X0)
% 3.51/3.75          | ~ (r1_tarski @ X0 @ 
% 3.51/3.75               (k5_waybel_0 @ sk_A @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))
% 3.51/3.75          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 3.51/3.75             (k1_yellow_0 @ sk_A @ 
% 3.51/3.75              (k5_waybel_0 @ sk_A @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 3.51/3.75      inference('demod', [status(thm)], ['33', '34'])).
% 3.51/3.75  thf('36', plain,
% 3.51/3.75      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.51/3.75         (k1_yellow_0 @ sk_A @ 
% 3.51/3.75          (k5_waybel_0 @ sk_A @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B))))
% 3.51/3.75        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 3.51/3.75        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('sup-', [status(thm)], ['21', '35'])).
% 3.51/3.75  thf('37', plain,
% 3.51/3.75      (((v2_struct_0 @ sk_A)
% 3.51/3.75        | ~ (v5_orders_2 @ sk_A)
% 3.51/3.75        | ~ (v1_yellow_0 @ sk_A)
% 3.51/3.75        | ~ (l1_orders_2 @ sk_A)
% 3.51/3.75        | ((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.51/3.75           (k1_yellow_0 @ sk_A @ 
% 3.51/3.75            (k5_waybel_0 @ sk_A @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 3.51/3.75      inference('sup-', [status(thm)], ['20', '36'])).
% 3.51/3.75  thf('38', plain, ((v5_orders_2 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('39', plain, ((v1_yellow_0 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('41', plain,
% 3.51/3.75      (((v2_struct_0 @ sk_A)
% 3.51/3.75        | ((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.51/3.75           (k1_yellow_0 @ sk_A @ 
% 3.51/3.75            (k5_waybel_0 @ sk_A @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 3.51/3.75      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 3.51/3.75  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('43', plain,
% 3.51/3.75      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.51/3.75         (k1_yellow_0 @ sk_A @ 
% 3.51/3.75          (k5_waybel_0 @ sk_A @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B))))
% 3.51/3.75        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('clc', [status(thm)], ['41', '42'])).
% 3.51/3.75  thf('44', plain,
% 3.51/3.75      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.51/3.75         (sk_C @ (u1_struct_0 @ sk_A) @ sk_B))
% 3.51/3.75        | ((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('sup+', [status(thm)], ['19', '43'])).
% 3.51/3.75  thf('45', plain,
% 3.51/3.75      ((((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.51/3.75           (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 3.51/3.75      inference('simplify', [status(thm)], ['44'])).
% 3.51/3.75  thf('46', plain,
% 3.51/3.75      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 3.51/3.75         (sk_C @ (u1_struct_0 @ sk_A) @ sk_B))
% 3.51/3.75        | ~ (l1_orders_2 @ sk_A)
% 3.51/3.75        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('sup+', [status(thm)], ['2', '45'])).
% 3.51/3.75  thf('47', plain, ((l1_orders_2 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('48', plain,
% 3.51/3.75      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 3.51/3.75         (sk_C @ (u1_struct_0 @ sk_A) @ sk_B))
% 3.51/3.75        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('demod', [status(thm)], ['46', '47'])).
% 3.51/3.75  thf('49', plain,
% 3.51/3.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 3.51/3.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 3.51/3.75      inference('split', [status(esa)], ['0'])).
% 3.51/3.75  thf('50', plain,
% 3.51/3.75      (![X0 : $i]:
% 3.51/3.75         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 3.51/3.75      inference('sup-', [status(thm)], ['4', '5'])).
% 3.51/3.75  thf('51', plain,
% 3.51/3.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 3.51/3.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 3.51/3.75      inference('sup-', [status(thm)], ['49', '50'])).
% 3.51/3.75  thf('52', plain,
% 3.51/3.75      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 3.51/3.75      inference('cnf', [status(esa)], [t1_subset])).
% 3.51/3.75  thf('53', plain,
% 3.51/3.75      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 3.51/3.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 3.51/3.75      inference('sup-', [status(thm)], ['51', '52'])).
% 3.51/3.75  thf('54', plain,
% 3.51/3.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf(d20_waybel_0, axiom,
% 3.51/3.75    (![A:$i]:
% 3.51/3.75     ( ( l1_orders_2 @ A ) =>
% 3.51/3.75       ( ![B:$i]:
% 3.51/3.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.51/3.75           ( ( v13_waybel_0 @ B @ A ) <=>
% 3.51/3.75             ( ![C:$i]:
% 3.51/3.75               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.51/3.75                 ( ![D:$i]:
% 3.51/3.75                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.51/3.75                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 3.51/3.75                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 3.51/3.75  thf('55', plain,
% 3.51/3.75      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.51/3.75         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 3.51/3.75          | ~ (v13_waybel_0 @ X21 @ X22)
% 3.51/3.75          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 3.51/3.75          | (r2_hidden @ X23 @ X21)
% 3.51/3.75          | ~ (r1_orders_2 @ X22 @ X24 @ X23)
% 3.51/3.75          | ~ (r2_hidden @ X24 @ X21)
% 3.51/3.75          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X22))
% 3.51/3.75          | ~ (l1_orders_2 @ X22))),
% 3.51/3.75      inference('cnf', [status(esa)], [d20_waybel_0])).
% 3.51/3.75  thf('56', plain,
% 3.51/3.75      (![X0 : $i, X1 : $i]:
% 3.51/3.75         (~ (l1_orders_2 @ sk_A)
% 3.51/3.75          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.51/3.75          | ~ (r2_hidden @ X0 @ sk_B)
% 3.51/3.75          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 3.51/3.75          | (r2_hidden @ X1 @ sk_B)
% 3.51/3.75          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.51/3.75          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 3.51/3.75      inference('sup-', [status(thm)], ['54', '55'])).
% 3.51/3.75  thf('57', plain, ((l1_orders_2 @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('58', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('59', plain,
% 3.51/3.75      (![X0 : $i, X1 : $i]:
% 3.51/3.75         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.51/3.75          | ~ (r2_hidden @ X0 @ sk_B)
% 3.51/3.75          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 3.51/3.75          | (r2_hidden @ X1 @ sk_B)
% 3.51/3.75          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('demod', [status(thm)], ['56', '57', '58'])).
% 3.51/3.75  thf('60', plain,
% 3.51/3.75      ((![X0 : $i]:
% 3.51/3.75          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.51/3.75           | (r2_hidden @ X0 @ sk_B)
% 3.51/3.75           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 3.51/3.75           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 3.51/3.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 3.51/3.75      inference('sup-', [status(thm)], ['53', '59'])).
% 3.51/3.75  thf('61', plain,
% 3.51/3.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 3.51/3.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 3.51/3.75      inference('split', [status(esa)], ['0'])).
% 3.51/3.75  thf('62', plain,
% 3.51/3.75      ((![X0 : $i]:
% 3.51/3.75          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.51/3.75           | (r2_hidden @ X0 @ sk_B)
% 3.51/3.75           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 3.51/3.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 3.51/3.75      inference('demod', [status(thm)], ['60', '61'])).
% 3.51/3.75  thf('63', plain,
% 3.51/3.75      (((((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75         | (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 3.51/3.75         | ~ (m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.51/3.75              (u1_struct_0 @ sk_A))))
% 3.51/3.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 3.51/3.75      inference('sup-', [status(thm)], ['48', '62'])).
% 3.51/3.75  thf('64', plain,
% 3.51/3.75      (((r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.51/3.75         (u1_struct_0 @ sk_A))
% 3.51/3.75        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('eq_fact', [status(thm)], ['7'])).
% 3.51/3.75  thf('65', plain,
% 3.51/3.75      (![X0 : $i, X1 : $i]:
% 3.51/3.75         (((X1) = (X0))
% 3.51/3.75          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 3.51/3.75          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 3.51/3.75      inference('cnf', [status(esa)], [t2_tarski])).
% 3.51/3.75  thf('66', plain,
% 3.51/3.75      ((((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75        | ~ (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 3.51/3.75        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('sup-', [status(thm)], ['64', '65'])).
% 3.51/3.75  thf('67', plain,
% 3.51/3.75      ((~ (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 3.51/3.75        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('simplify', [status(thm)], ['66'])).
% 3.51/3.75  thf('68', plain,
% 3.51/3.75      (((~ (m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.51/3.75            (u1_struct_0 @ sk_A))
% 3.51/3.75         | ((sk_B) = (u1_struct_0 @ sk_A))))
% 3.51/3.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 3.51/3.75      inference('clc', [status(thm)], ['63', '67'])).
% 3.51/3.75  thf('69', plain,
% 3.51/3.75      ((((sk_B) = (u1_struct_0 @ sk_A))
% 3.51/3.75        | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.51/3.75           (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('sup-', [status(thm)], ['8', '9'])).
% 3.51/3.75  thf('70', plain,
% 3.51/3.75      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 3.51/3.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 3.51/3.75      inference('clc', [status(thm)], ['68', '69'])).
% 3.51/3.75  thf('71', plain,
% 3.51/3.75      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 3.51/3.75        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('72', plain,
% 3.51/3.75      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 3.51/3.75         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 3.51/3.75      inference('split', [status(esa)], ['71'])).
% 3.51/3.75  thf('73', plain,
% 3.51/3.75      (((v1_subset_1 @ sk_B @ sk_B))
% 3.51/3.75         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 3.51/3.75             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 3.51/3.75      inference('sup+', [status(thm)], ['70', '72'])).
% 3.51/3.75  thf(d7_subset_1, axiom,
% 3.51/3.75    (![A:$i,B:$i]:
% 3.51/3.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.51/3.75       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 3.51/3.75  thf('74', plain,
% 3.51/3.75      (![X27 : $i, X28 : $i]:
% 3.51/3.75         (~ (v1_subset_1 @ X28 @ X27)
% 3.51/3.75          | ((X28) != (X27))
% 3.51/3.75          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 3.51/3.75      inference('cnf', [status(esa)], [d7_subset_1])).
% 3.51/3.75  thf('75', plain,
% 3.51/3.75      (![X27 : $i]:
% 3.51/3.75         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X27))
% 3.51/3.75          | ~ (v1_subset_1 @ X27 @ X27))),
% 3.51/3.75      inference('simplify', [status(thm)], ['74'])).
% 3.51/3.75  thf(dt_k2_subset_1, axiom,
% 3.51/3.75    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 3.51/3.75  thf('76', plain,
% 3.51/3.75      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 3.51/3.75      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 3.51/3.75  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 3.51/3.75  thf('77', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 3.51/3.75      inference('cnf', [status(esa)], [d4_subset_1])).
% 3.51/3.75  thf('78', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 3.51/3.75      inference('demod', [status(thm)], ['76', '77'])).
% 3.51/3.75  thf('79', plain, (![X27 : $i]: ~ (v1_subset_1 @ X27 @ X27)),
% 3.51/3.75      inference('demod', [status(thm)], ['75', '78'])).
% 3.51/3.75  thf('80', plain,
% 3.51/3.75      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 3.51/3.75       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('sup-', [status(thm)], ['73', '79'])).
% 3.51/3.75  thf('81', plain,
% 3.51/3.75      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 3.51/3.75       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('split', [status(esa)], ['71'])).
% 3.51/3.75  thf('82', plain,
% 3.51/3.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.51/3.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.75  thf('83', plain,
% 3.51/3.75      (![X27 : $i, X28 : $i]:
% 3.51/3.75         (((X28) = (X27))
% 3.51/3.75          | (v1_subset_1 @ X28 @ X27)
% 3.51/3.75          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 3.51/3.75      inference('cnf', [status(esa)], [d7_subset_1])).
% 3.51/3.75  thf('84', plain,
% 3.51/3.75      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 3.51/3.76        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['82', '83'])).
% 3.51/3.76  thf('85', plain,
% 3.51/3.76      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 3.51/3.76         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 3.51/3.76      inference('split', [status(esa)], ['0'])).
% 3.51/3.76  thf('86', plain,
% 3.51/3.76      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 3.51/3.76         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 3.51/3.76      inference('sup-', [status(thm)], ['84', '85'])).
% 3.51/3.76  thf(dt_k3_yellow_0, axiom,
% 3.51/3.76    (![A:$i]:
% 3.51/3.76     ( ( l1_orders_2 @ A ) =>
% 3.51/3.76       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 3.51/3.76  thf('87', plain,
% 3.51/3.76      (![X16 : $i]:
% 3.51/3.76         ((m1_subset_1 @ (k3_yellow_0 @ X16) @ (u1_struct_0 @ X16))
% 3.51/3.76          | ~ (l1_orders_2 @ X16))),
% 3.51/3.76      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 3.51/3.76  thf(t2_subset, axiom,
% 3.51/3.76    (![A:$i,B:$i]:
% 3.51/3.76     ( ( m1_subset_1 @ A @ B ) =>
% 3.51/3.76       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 3.51/3.76  thf('88', plain,
% 3.51/3.76      (![X10 : $i, X11 : $i]:
% 3.51/3.76         ((r2_hidden @ X10 @ X11)
% 3.51/3.76          | (v1_xboole_0 @ X11)
% 3.51/3.76          | ~ (m1_subset_1 @ X10 @ X11))),
% 3.51/3.76      inference('cnf', [status(esa)], [t2_subset])).
% 3.51/3.76  thf('89', plain,
% 3.51/3.76      (![X0 : $i]:
% 3.51/3.76         (~ (l1_orders_2 @ X0)
% 3.51/3.76          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 3.51/3.76          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['87', '88'])).
% 3.51/3.76  thf('90', plain,
% 3.51/3.76      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 3.51/3.76         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.51/3.76         | ~ (l1_orders_2 @ sk_A)))
% 3.51/3.76         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 3.51/3.76      inference('sup+', [status(thm)], ['86', '89'])).
% 3.51/3.76  thf('91', plain,
% 3.51/3.76      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 3.51/3.76         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 3.51/3.76      inference('sup-', [status(thm)], ['84', '85'])).
% 3.51/3.76  thf('92', plain, ((l1_orders_2 @ sk_A)),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('93', plain,
% 3.51/3.76      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B) | (v1_xboole_0 @ sk_B)))
% 3.51/3.76         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 3.51/3.76      inference('demod', [status(thm)], ['90', '91', '92'])).
% 3.51/3.76  thf('94', plain, (~ (v1_xboole_0 @ sk_B)),
% 3.51/3.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.51/3.76  thf('95', plain,
% 3.51/3.76      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 3.51/3.76         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 3.51/3.76      inference('clc', [status(thm)], ['93', '94'])).
% 3.51/3.76  thf('96', plain,
% 3.51/3.76      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 3.51/3.76         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 3.51/3.76      inference('split', [status(esa)], ['71'])).
% 3.51/3.76  thf('97', plain,
% 3.51/3.76      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 3.51/3.76       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.51/3.76      inference('sup-', [status(thm)], ['95', '96'])).
% 3.51/3.76  thf('98', plain, ($false),
% 3.51/3.76      inference('sat_resolution*', [status(thm)], ['1', '80', '81', '97'])).
% 3.51/3.76  
% 3.51/3.76  % SZS output end Refutation
% 3.51/3.76  
% 3.51/3.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
