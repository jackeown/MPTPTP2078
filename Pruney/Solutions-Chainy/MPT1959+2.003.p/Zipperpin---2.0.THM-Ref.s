%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nqKB2jejFu

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:09 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 188 expanded)
%              Number of leaves         :   32 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  827 (2728 expanded)
%              Number of equality atoms :   26 (  38 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ X0 )
      | ( sk_B = X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( r1_orders_2 @ X15 @ ( k3_yellow_0 @ X15 ) @ X14 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v1_yellow_0 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('11',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v13_waybel_0 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( r2_hidden @ X18 @ X16 )
      | ~ ( r1_orders_2 @ X17 @ X19 @ X18 )
      | ~ ( r2_hidden @ X19 @ X16 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('41',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['30','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('45',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['45','47'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('49',plain,(
    ! [X5: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('50',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('51',plain,(
    ! [X5: $i] :
      ~ ( v1_subset_1 @ X5 @ X5 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['46'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('55',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X21 = X20 )
      | ( v1_subset_1 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('56',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('59',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('60',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('64',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('69',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','52','53','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nqKB2jejFu
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 139 iterations in 0.112s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.37/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.37/0.57  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.37/0.57  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.37/0.57  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.37/0.57  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.37/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.37/0.57  thf(t8_waybel_7, conjecture,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.57         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.37/0.57         ( l1_orders_2 @ A ) ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.37/0.57             ( v13_waybel_0 @ B @ A ) & 
% 0.37/0.57             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.57           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.37/0.57             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i]:
% 0.37/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.57            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.37/0.57            ( l1_orders_2 @ A ) ) =>
% 0.37/0.57          ( ![B:$i]:
% 0.37/0.57            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.37/0.57                ( v13_waybel_0 @ B @ A ) & 
% 0.37/0.57                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.57              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.37/0.57                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.37/0.57        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.37/0.57       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf(t2_tarski, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.37/0.57       ( ( A ) = ( B ) ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (((X1) = (X0))
% 0.37/0.57          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.37/0.57          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_tarski])).
% 0.37/0.57  thf(t1_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.37/0.57      inference('cnf', [status(esa)], [t1_subset])).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.37/0.57          | ((X1) = (X0))
% 0.37/0.57          | (m1_subset_1 @ (sk_C @ X0 @ X1) @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t4_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.37/0.57       ( m1_subset_1 @ A @ C ) ))).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X10 @ X11)
% 0.37/0.57          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.37/0.57          | (m1_subset_1 @ X10 @ X12))),
% 0.37/0.57      inference('cnf', [status(esa)], [t4_subset])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((m1_subset_1 @ (sk_C @ X0 @ sk_B) @ X0)
% 0.37/0.57          | ((sk_B) = (X0))
% 0.37/0.57          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (((m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.57         (u1_struct_0 @ sk_A))
% 0.37/0.57        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('eq_fact', [status(thm)], ['8'])).
% 0.37/0.57  thf(t44_yellow_0, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.37/0.57         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.57           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X14 : $i, X15 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.37/0.57          | (r1_orders_2 @ X15 @ (k3_yellow_0 @ X15) @ X14)
% 0.37/0.57          | ~ (l1_orders_2 @ X15)
% 0.37/0.57          | ~ (v1_yellow_0 @ X15)
% 0.37/0.57          | ~ (v5_orders_2 @ X15)
% 0.37/0.57          | (v2_struct_0 @ X15))),
% 0.37/0.57      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.37/0.57        | (v2_struct_0 @ sk_A)
% 0.37/0.57        | ~ (v5_orders_2 @ sk_A)
% 0.37/0.57        | ~ (v1_yellow_0 @ sk_A)
% 0.37/0.57        | ~ (l1_orders_2 @ sk_A)
% 0.37/0.57        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.37/0.57           (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.57  thf('12', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('13', plain, ((v1_yellow_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('14', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.37/0.57        | (v2_struct_0 @ sk_A)
% 0.37/0.57        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.37/0.57           (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.37/0.57  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.37/0.57         (sk_C @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.37/0.57        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['15', '16'])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(d20_waybel_0, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_orders_2 @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.37/0.57             ( ![C:$i]:
% 0.37/0.57               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.57                 ( ![D:$i]:
% 0.37/0.57                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.57                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.37/0.57                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.57          | ~ (v13_waybel_0 @ X16 @ X17)
% 0.37/0.57          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.37/0.57          | (r2_hidden @ X18 @ X16)
% 0.37/0.57          | ~ (r1_orders_2 @ X17 @ X19 @ X18)
% 0.37/0.57          | ~ (r2_hidden @ X19 @ X16)
% 0.37/0.57          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.37/0.57          | ~ (l1_orders_2 @ X17))),
% 0.37/0.57      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (l1_orders_2 @ sk_A)
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.57          | ~ (r2_hidden @ X0 @ sk_B)
% 0.37/0.57          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.37/0.57          | (r2_hidden @ X1 @ sk_B)
% 0.37/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.37/0.57          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.57  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('25', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.57          | ~ (r2_hidden @ X0 @ sk_B)
% 0.37/0.57          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.37/0.57          | (r2_hidden @ X1 @ sk_B)
% 0.37/0.57          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      ((![X0 : $i]:
% 0.37/0.57          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.57           | (r2_hidden @ X0 @ sk_B)
% 0.37/0.57           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.37/0.57           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['20', '26'])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      ((![X0 : $i]:
% 0.37/0.57          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.57           | (r2_hidden @ X0 @ sk_B)
% 0.37/0.57           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.37/0.57         | (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.37/0.57         | ~ (m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.57              (u1_struct_0 @ sk_A))))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['17', '29'])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (((m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.57         (u1_struct_0 @ sk_A))
% 0.37/0.57        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('eq_fact', [status(thm)], ['8'])).
% 0.37/0.57  thf(t2_subset, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X8 : $i, X9 : $i]:
% 0.37/0.57         ((r2_hidden @ X8 @ X9)
% 0.37/0.57          | (v1_xboole_0 @ X9)
% 0.37/0.57          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.37/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.57        | (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.57           (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(cc1_subset_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      (![X3 : $i, X4 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.37/0.57          | (v1_xboole_0 @ X3)
% 0.37/0.57          | ~ (v1_xboole_0 @ X4))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.57  thf('37', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('38', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('clc', [status(thm)], ['36', '37'])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (((r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.57         (u1_struct_0 @ sk_A))
% 0.37/0.57        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('clc', [status(thm)], ['33', '38'])).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (((X1) = (X0))
% 0.37/0.57          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.37/0.57          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_tarski])).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.37/0.57        | ~ (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.37/0.57        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      ((~ (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.37/0.57        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['41'])).
% 0.37/0.57  thf('43', plain,
% 0.37/0.57      (((~ (m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.57            (u1_struct_0 @ sk_A))
% 0.37/0.57         | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.57      inference('clc', [status(thm)], ['30', '42'])).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      (((m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.37/0.57         (u1_struct_0 @ sk_A))
% 0.37/0.57        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('eq_fact', [status(thm)], ['8'])).
% 0.37/0.57  thf('45', plain,
% 0.37/0.57      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.37/0.57         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.57      inference('clc', [status(thm)], ['43', '44'])).
% 0.37/0.57  thf('46', plain,
% 0.37/0.57      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.37/0.57        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('47', plain,
% 0.37/0.57      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.37/0.57         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('split', [status(esa)], ['46'])).
% 0.37/0.57  thf('48', plain,
% 0.37/0.57      (((v1_subset_1 @ sk_B @ sk_B))
% 0.37/0.57         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.37/0.57             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['45', '47'])).
% 0.37/0.57  thf(fc14_subset_1, axiom,
% 0.37/0.57    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.37/0.57  thf('49', plain, (![X5 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X5) @ X5)),
% 0.37/0.57      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.37/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.37/0.57  thf('50', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.37/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.37/0.57  thf('51', plain, (![X5 : $i]: ~ (v1_subset_1 @ X5 @ X5)),
% 0.37/0.57      inference('demod', [status(thm)], ['49', '50'])).
% 0.37/0.57  thf('52', plain,
% 0.37/0.57      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.37/0.57       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['48', '51'])).
% 0.37/0.57  thf('53', plain,
% 0.37/0.57      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.37/0.57       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['46'])).
% 0.37/0.57  thf('54', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(d7_subset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.57       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.37/0.57  thf('55', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i]:
% 0.37/0.57         (((X21) = (X20))
% 0.37/0.57          | (v1_subset_1 @ X21 @ X20)
% 0.37/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.37/0.57  thf('56', plain,
% 0.37/0.57      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.37/0.57        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.57  thf('57', plain,
% 0.37/0.57      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.37/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('58', plain,
% 0.37/0.57      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.37/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.57  thf(dt_k3_yellow_0, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_orders_2 @ A ) =>
% 0.37/0.57       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.37/0.57  thf('59', plain,
% 0.37/0.57      (![X13 : $i]:
% 0.37/0.57         ((m1_subset_1 @ (k3_yellow_0 @ X13) @ (u1_struct_0 @ X13))
% 0.37/0.57          | ~ (l1_orders_2 @ X13))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.37/0.57  thf('60', plain,
% 0.37/0.57      (![X8 : $i, X9 : $i]:
% 0.37/0.57         ((r2_hidden @ X8 @ X9)
% 0.37/0.57          | (v1_xboole_0 @ X9)
% 0.37/0.57          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.57  thf('61', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (l1_orders_2 @ X0)
% 0.37/0.57          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.37/0.57          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.57  thf('62', plain,
% 0.37/0.57      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.37/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.57         | ~ (l1_orders_2 @ sk_A)))
% 0.37/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['58', '61'])).
% 0.37/0.57  thf('63', plain,
% 0.37/0.57      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.37/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.57  thf('64', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('65', plain,
% 0.37/0.57      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B) | (v1_xboole_0 @ sk_B)))
% 0.37/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.37/0.57  thf('66', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('67', plain,
% 0.37/0.57      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.37/0.57         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('clc', [status(thm)], ['65', '66'])).
% 0.37/0.57  thf('68', plain,
% 0.37/0.57      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.37/0.57         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.57      inference('split', [status(esa)], ['46'])).
% 0.37/0.57  thf('69', plain,
% 0.37/0.57      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.37/0.57       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.37/0.57  thf('70', plain, ($false),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['1', '52', '53', '69'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
