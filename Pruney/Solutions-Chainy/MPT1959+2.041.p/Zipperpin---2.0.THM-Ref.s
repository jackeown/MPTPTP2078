%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zE37US2lqu

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:15 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 183 expanded)
%              Number of leaves         :   31 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  804 (2613 expanded)
%              Number of equality atoms :   24 (  35 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

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

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_B_1 @ X0 ) @ X0 )
      | ( X0 = sk_B_1 )
      | ( r2_hidden @ ( sk_C @ sk_B_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( m1_subset_1 @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r1_orders_2 @ X18 @ ( k3_yellow_0 @ X18 ) @ X17 )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v1_yellow_0 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('13',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('22',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('24',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v13_waybel_0 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( r2_hidden @ X21 @ X19 )
      | ~ ( r1_orders_2 @ X20 @ X22 @ X21 )
      | ~ ( r2_hidden @ X22 @ X19 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['19','33'])).

thf('35',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('36',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('38',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('41',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['41','43'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('45',plain,(
    ! [X12: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('46',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('47',plain,(
    ! [X12: $i] :
      ~ ( v1_subset_1 @ X12 @ X12 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['42'])).

thf('50',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('51',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X24 = X23 )
      | ( v1_subset_1 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('52',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('55',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('60',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['42'])).

thf('65',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','48','49','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zE37US2lqu
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.98/1.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.98/1.19  % Solved by: fo/fo7.sh
% 0.98/1.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.98/1.19  % done 767 iterations in 0.748s
% 0.98/1.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.98/1.19  % SZS output start Refutation
% 0.98/1.19  thf(sk_A_type, type, sk_A: $i).
% 0.98/1.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.98/1.19  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.98/1.19  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.98/1.19  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.98/1.19  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.98/1.19  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.98/1.19  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.98/1.19  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.98/1.19  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.98/1.19  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.98/1.19  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.98/1.19  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.98/1.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.98/1.19  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.98/1.19  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.98/1.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.98/1.19  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.98/1.19  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.98/1.19  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.98/1.19  thf(t8_waybel_7, conjecture,
% 0.98/1.19    (![A:$i]:
% 0.98/1.19     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.98/1.19         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.98/1.19         ( l1_orders_2 @ A ) ) =>
% 0.98/1.19       ( ![B:$i]:
% 0.98/1.19         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.98/1.19             ( v13_waybel_0 @ B @ A ) & 
% 0.98/1.19             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.98/1.19           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.98/1.19             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.98/1.19  thf(zf_stmt_0, negated_conjecture,
% 0.98/1.19    (~( ![A:$i]:
% 0.98/1.19        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.98/1.19            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.98/1.19            ( l1_orders_2 @ A ) ) =>
% 0.98/1.19          ( ![B:$i]:
% 0.98/1.19            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.98/1.19                ( v13_waybel_0 @ B @ A ) & 
% 0.98/1.19                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.98/1.19              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.98/1.19                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.98/1.19    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.98/1.19  thf('0', plain,
% 0.98/1.19      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.98/1.19        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.19  thf('1', plain,
% 0.98/1.19      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.98/1.19       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.19      inference('split', [status(esa)], ['0'])).
% 0.98/1.19  thf(t2_tarski, axiom,
% 0.98/1.19    (![A:$i,B:$i]:
% 0.98/1.19     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.98/1.19       ( ( A ) = ( B ) ) ))).
% 0.98/1.19  thf('2', plain,
% 0.98/1.19      (![X3 : $i, X4 : $i]:
% 0.98/1.19         (((X4) = (X3))
% 0.98/1.19          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 0.98/1.19          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 0.98/1.19      inference('cnf', [status(esa)], [t2_tarski])).
% 0.98/1.19  thf('3', plain,
% 0.98/1.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.19  thf(l3_subset_1, axiom,
% 0.98/1.19    (![A:$i,B:$i]:
% 0.98/1.19     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.19       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.98/1.19  thf('4', plain,
% 0.98/1.19      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.98/1.19         (~ (r2_hidden @ X9 @ X10)
% 0.98/1.19          | (r2_hidden @ X9 @ X11)
% 0.98/1.19          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.98/1.19      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.98/1.19  thf('5', plain,
% 0.98/1.19      (![X0 : $i]:
% 0.98/1.19         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.98/1.19      inference('sup-', [status(thm)], ['3', '4'])).
% 0.98/1.19  thf('6', plain,
% 0.98/1.19      (![X0 : $i]:
% 0.98/1.19         ((r2_hidden @ (sk_C @ sk_B_1 @ X0) @ X0)
% 0.98/1.19          | ((X0) = (sk_B_1))
% 0.98/1.19          | (r2_hidden @ (sk_C @ sk_B_1 @ X0) @ (u1_struct_0 @ sk_A)))),
% 0.98/1.19      inference('sup-', [status(thm)], ['2', '5'])).
% 0.98/1.19  thf('7', plain,
% 0.98/1.19      (((r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.98/1.19         (u1_struct_0 @ sk_A))
% 0.98/1.19        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.98/1.19      inference('eq_fact', [status(thm)], ['6'])).
% 0.98/1.19  thf(d2_subset_1, axiom,
% 0.98/1.19    (![A:$i,B:$i]:
% 0.98/1.19     ( ( ( v1_xboole_0 @ A ) =>
% 0.98/1.19         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.98/1.19       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.98/1.19         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.98/1.19  thf('8', plain,
% 0.98/1.19      (![X5 : $i, X6 : $i]:
% 0.98/1.19         (~ (r2_hidden @ X5 @ X6)
% 0.98/1.19          | (m1_subset_1 @ X5 @ X6)
% 0.98/1.19          | (v1_xboole_0 @ X6))),
% 0.98/1.19      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.98/1.19  thf(d1_xboole_0, axiom,
% 0.98/1.19    (![A:$i]:
% 0.98/1.19     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.98/1.19  thf('9', plain,
% 0.98/1.19      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.98/1.19      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.98/1.19  thf('10', plain,
% 0.98/1.19      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 0.98/1.19      inference('clc', [status(thm)], ['8', '9'])).
% 0.98/1.19  thf('11', plain,
% 0.98/1.19      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.19        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.98/1.19           (u1_struct_0 @ sk_A)))),
% 0.98/1.19      inference('sup-', [status(thm)], ['7', '10'])).
% 0.98/1.19  thf(t44_yellow_0, axiom,
% 0.98/1.19    (![A:$i]:
% 0.98/1.19     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.98/1.19         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.98/1.19       ( ![B:$i]:
% 0.98/1.19         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.98/1.19           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.98/1.19  thf('12', plain,
% 0.98/1.19      (![X17 : $i, X18 : $i]:
% 0.98/1.19         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.98/1.19          | (r1_orders_2 @ X18 @ (k3_yellow_0 @ X18) @ X17)
% 0.98/1.19          | ~ (l1_orders_2 @ X18)
% 0.98/1.19          | ~ (v1_yellow_0 @ X18)
% 0.98/1.19          | ~ (v5_orders_2 @ X18)
% 0.98/1.19          | (v2_struct_0 @ X18))),
% 0.98/1.19      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.98/1.19  thf('13', plain,
% 0.98/1.19      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.19        | (v2_struct_0 @ sk_A)
% 0.98/1.19        | ~ (v5_orders_2 @ sk_A)
% 0.98/1.19        | ~ (v1_yellow_0 @ sk_A)
% 0.98/1.19        | ~ (l1_orders_2 @ sk_A)
% 0.98/1.19        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.98/1.19           (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.19      inference('sup-', [status(thm)], ['11', '12'])).
% 0.98/1.19  thf('14', plain, ((v5_orders_2 @ sk_A)),
% 0.98/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.19  thf('15', plain, ((v1_yellow_0 @ sk_A)),
% 0.98/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.19  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 0.98/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.19  thf('17', plain,
% 0.98/1.19      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.19        | (v2_struct_0 @ sk_A)
% 0.98/1.19        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.98/1.19           (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.19      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.98/1.19  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.98/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.19  thf('19', plain,
% 0.98/1.19      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.98/1.19         (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.19        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.98/1.19      inference('clc', [status(thm)], ['17', '18'])).
% 0.98/1.19  thf('20', plain,
% 0.98/1.19      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.98/1.19         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.19      inference('split', [status(esa)], ['0'])).
% 0.98/1.19  thf('21', plain,
% 0.98/1.19      (![X0 : $i]:
% 0.98/1.19         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.98/1.19      inference('sup-', [status(thm)], ['3', '4'])).
% 0.98/1.19  thf('22', plain,
% 0.98/1.19      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.98/1.19         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.19      inference('sup-', [status(thm)], ['20', '21'])).
% 0.98/1.19  thf('23', plain,
% 0.98/1.19      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 0.98/1.19      inference('clc', [status(thm)], ['8', '9'])).
% 0.98/1.19  thf('24', plain,
% 0.98/1.19      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.98/1.19         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.19      inference('sup-', [status(thm)], ['22', '23'])).
% 0.98/1.19  thf('25', plain,
% 0.98/1.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.19  thf(d20_waybel_0, axiom,
% 0.98/1.19    (![A:$i]:
% 0.98/1.19     ( ( l1_orders_2 @ A ) =>
% 0.98/1.19       ( ![B:$i]:
% 0.98/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.98/1.19           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.98/1.19             ( ![C:$i]:
% 0.98/1.19               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.98/1.19                 ( ![D:$i]:
% 0.98/1.19                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.98/1.19                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.98/1.19                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.98/1.19  thf('26', plain,
% 0.98/1.19      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.98/1.19         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.98/1.19          | ~ (v13_waybel_0 @ X19 @ X20)
% 0.98/1.19          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.98/1.19          | (r2_hidden @ X21 @ X19)
% 0.98/1.19          | ~ (r1_orders_2 @ X20 @ X22 @ X21)
% 0.98/1.19          | ~ (r2_hidden @ X22 @ X19)
% 0.98/1.19          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 0.98/1.19          | ~ (l1_orders_2 @ X20))),
% 0.98/1.19      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.98/1.19  thf('27', plain,
% 0.98/1.19      (![X0 : $i, X1 : $i]:
% 0.98/1.19         (~ (l1_orders_2 @ sk_A)
% 0.98/1.19          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.98/1.19          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.98/1.19          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.98/1.19          | (r2_hidden @ X1 @ sk_B_1)
% 0.98/1.19          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.98/1.19          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 0.98/1.19      inference('sup-', [status(thm)], ['25', '26'])).
% 0.98/1.19  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 0.98/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.19  thf('29', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 0.98/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.19  thf('30', plain,
% 0.98/1.19      (![X0 : $i, X1 : $i]:
% 0.98/1.19         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.98/1.19          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.98/1.19          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.98/1.19          | (r2_hidden @ X1 @ sk_B_1)
% 0.98/1.19          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.19      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.98/1.19  thf('31', plain,
% 0.98/1.19      ((![X0 : $i]:
% 0.98/1.19          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.98/1.19           | (r2_hidden @ X0 @ sk_B_1)
% 0.98/1.19           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.98/1.19           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.98/1.19         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.19      inference('sup-', [status(thm)], ['24', '30'])).
% 0.98/1.19  thf('32', plain,
% 0.98/1.19      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.98/1.19         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.19      inference('split', [status(esa)], ['0'])).
% 0.98/1.19  thf('33', plain,
% 0.98/1.19      ((![X0 : $i]:
% 0.98/1.19          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.98/1.19           | (r2_hidden @ X0 @ sk_B_1)
% 0.98/1.19           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.98/1.19         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.19      inference('demod', [status(thm)], ['31', '32'])).
% 0.98/1.19  thf('34', plain,
% 0.98/1.19      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.19         | (r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 0.98/1.19         | ~ (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.98/1.19              (u1_struct_0 @ sk_A))))
% 0.98/1.19         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.19      inference('sup-', [status(thm)], ['19', '33'])).
% 0.98/1.19  thf('35', plain,
% 0.98/1.19      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.19        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.98/1.19           (u1_struct_0 @ sk_A)))),
% 0.98/1.19      inference('sup-', [status(thm)], ['7', '10'])).
% 0.98/1.19  thf('36', plain,
% 0.98/1.19      ((((r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 0.98/1.19         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.98/1.19         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.19      inference('clc', [status(thm)], ['34', '35'])).
% 0.98/1.19  thf('37', plain,
% 0.98/1.19      (![X3 : $i, X4 : $i]:
% 0.98/1.19         (((X4) = (X3))
% 0.98/1.19          | ~ (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 0.98/1.19          | ~ (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 0.98/1.19      inference('cnf', [status(esa)], [t2_tarski])).
% 0.98/1.19  thf('38', plain,
% 0.98/1.19      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.98/1.19         | ~ (r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.98/1.19              (u1_struct_0 @ sk_A))
% 0.98/1.19         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.98/1.19         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.19      inference('sup-', [status(thm)], ['36', '37'])).
% 0.98/1.19  thf('39', plain,
% 0.98/1.19      (((~ (r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.98/1.19            (u1_struct_0 @ sk_A))
% 0.98/1.19         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.98/1.19         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.19      inference('simplify', [status(thm)], ['38'])).
% 0.98/1.19  thf('40', plain,
% 0.98/1.19      (((r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.98/1.19         (u1_struct_0 @ sk_A))
% 0.98/1.19        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.98/1.19      inference('eq_fact', [status(thm)], ['6'])).
% 0.98/1.19  thf('41', plain,
% 0.98/1.19      ((((u1_struct_0 @ sk_A) = (sk_B_1)))
% 0.98/1.19         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.19      inference('clc', [status(thm)], ['39', '40'])).
% 0.98/1.19  thf('42', plain,
% 0.98/1.19      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.98/1.19        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.19  thf('43', plain,
% 0.98/1.19      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.19         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.19      inference('split', [status(esa)], ['42'])).
% 0.98/1.19  thf('44', plain,
% 0.98/1.19      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.98/1.19         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 0.98/1.19             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.19      inference('sup+', [status(thm)], ['41', '43'])).
% 0.98/1.19  thf(fc14_subset_1, axiom,
% 0.98/1.19    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.98/1.19  thf('45', plain, (![X12 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X12) @ X12)),
% 0.98/1.19      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.98/1.19  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.98/1.19  thf('46', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.98/1.19      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.98/1.19  thf('47', plain, (![X12 : $i]: ~ (v1_subset_1 @ X12 @ X12)),
% 0.98/1.19      inference('demod', [status(thm)], ['45', '46'])).
% 0.98/1.19  thf('48', plain,
% 0.98/1.19      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.98/1.19       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.19      inference('sup-', [status(thm)], ['44', '47'])).
% 0.98/1.19  thf('49', plain,
% 0.98/1.19      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.98/1.19       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.19      inference('split', [status(esa)], ['42'])).
% 0.98/1.19  thf('50', plain,
% 0.98/1.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.19  thf(d7_subset_1, axiom,
% 0.98/1.19    (![A:$i,B:$i]:
% 0.98/1.19     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.98/1.19       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.98/1.19  thf('51', plain,
% 0.98/1.19      (![X23 : $i, X24 : $i]:
% 0.98/1.19         (((X24) = (X23))
% 0.98/1.19          | (v1_subset_1 @ X24 @ X23)
% 0.98/1.19          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.98/1.19      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.98/1.19  thf('52', plain,
% 0.98/1.19      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.98/1.19        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.98/1.19      inference('sup-', [status(thm)], ['50', '51'])).
% 0.98/1.19  thf('53', plain,
% 0.98/1.19      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.98/1.19         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.19      inference('split', [status(esa)], ['0'])).
% 0.98/1.19  thf('54', plain,
% 0.98/1.19      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.98/1.19         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.19      inference('sup-', [status(thm)], ['52', '53'])).
% 0.98/1.19  thf(dt_k3_yellow_0, axiom,
% 0.98/1.19    (![A:$i]:
% 0.98/1.19     ( ( l1_orders_2 @ A ) =>
% 0.98/1.19       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.98/1.19  thf('55', plain,
% 0.98/1.19      (![X16 : $i]:
% 0.98/1.19         ((m1_subset_1 @ (k3_yellow_0 @ X16) @ (u1_struct_0 @ X16))
% 0.98/1.19          | ~ (l1_orders_2 @ X16))),
% 0.98/1.19      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.98/1.19  thf('56', plain,
% 0.98/1.19      (![X5 : $i, X6 : $i]:
% 0.98/1.19         (~ (m1_subset_1 @ X5 @ X6)
% 0.98/1.19          | (r2_hidden @ X5 @ X6)
% 0.98/1.19          | (v1_xboole_0 @ X6))),
% 0.98/1.19      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.98/1.19  thf('57', plain,
% 0.98/1.19      (![X0 : $i]:
% 0.98/1.19         (~ (l1_orders_2 @ X0)
% 0.98/1.19          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.98/1.19          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.98/1.19      inference('sup-', [status(thm)], ['55', '56'])).
% 0.98/1.19  thf('58', plain,
% 0.98/1.19      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.98/1.19         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.98/1.19         | ~ (l1_orders_2 @ sk_A)))
% 0.98/1.19         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.19      inference('sup+', [status(thm)], ['54', '57'])).
% 0.98/1.19  thf('59', plain,
% 0.98/1.20      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.98/1.20         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.20      inference('sup-', [status(thm)], ['52', '53'])).
% 0.98/1.20  thf('60', plain, ((l1_orders_2 @ sk_A)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('61', plain,
% 0.98/1.20      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1) | (v1_xboole_0 @ sk_B_1)))
% 0.98/1.20         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.20      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.98/1.20  thf('62', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.98/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.20  thf('63', plain,
% 0.98/1.20      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.98/1.20         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.98/1.20      inference('clc', [status(thm)], ['61', '62'])).
% 0.98/1.20  thf('64', plain,
% 0.98/1.20      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.98/1.20         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.98/1.20      inference('split', [status(esa)], ['42'])).
% 0.98/1.20  thf('65', plain,
% 0.98/1.20      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.98/1.20       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.98/1.20      inference('sup-', [status(thm)], ['63', '64'])).
% 0.98/1.20  thf('66', plain, ($false),
% 0.98/1.20      inference('sat_resolution*', [status(thm)], ['1', '48', '49', '65'])).
% 0.98/1.20  
% 0.98/1.20  % SZS output end Refutation
% 0.98/1.20  
% 0.98/1.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
