%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h1sQgXc2oV

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:09 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 182 expanded)
%              Number of leaves         :   32 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  851 (2581 expanded)
%              Number of equality atoms :   26 (  36 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ X14 @ X16 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( r1_orders_2 @ X19 @ ( k3_yellow_0 @ X19 ) @ X18 )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v1_yellow_0 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
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

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('49',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_subset_1 @ X25 @ X24 )
      | ( X25 != X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('50',plain,(
    ! [X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( v1_subset_1 @ X24 @ X24 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['51'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('53',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X24: $i] :
      ~ ( v1_subset_1 @ X24 @ X24 ) ),
    inference(demod,[status(thm)],['50','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['46'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( v1_subset_1 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('60',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('63',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('64',plain,
    ( ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('68',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('72',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','56','57','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h1sQgXc2oV
% 0.16/0.37  % Computer   : n017.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 17:48:47 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 141 iterations in 0.122s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.61  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.43/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.43/0.61  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.43/0.61  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.43/0.61  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.43/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.43/0.61  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.43/0.61  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.43/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.43/0.61  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.43/0.61  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.43/0.61  thf(t8_waybel_7, conjecture,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.43/0.61         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.43/0.61         ( l1_orders_2 @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.43/0.61             ( v13_waybel_0 @ B @ A ) & 
% 0.43/0.61             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.61           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.43/0.61             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i]:
% 0.43/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.43/0.61            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.43/0.61            ( l1_orders_2 @ A ) ) =>
% 0.43/0.61          ( ![B:$i]:
% 0.43/0.61            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.43/0.61                ( v13_waybel_0 @ B @ A ) & 
% 0.43/0.61                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.61              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.43/0.61                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.43/0.61        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.43/0.61       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf(t2_tarski, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.43/0.61       ( ( A ) = ( B ) ) ))).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((X1) = (X0))
% 0.43/0.61          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.43/0.61          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [t2_tarski])).
% 0.43/0.61  thf(t1_subset, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.43/0.61      inference('cnf', [status(esa)], [t1_subset])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.43/0.61          | ((X1) = (X0))
% 0.43/0.61          | (m1_subset_1 @ (sk_C @ X0 @ X1) @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t4_subset, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.43/0.61       ( m1_subset_1 @ A @ C ) ))).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X14 @ X15)
% 0.43/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.43/0.61          | (m1_subset_1 @ X14 @ X16))),
% 0.43/0.61      inference('cnf', [status(esa)], [t4_subset])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((m1_subset_1 @ (sk_C @ X0 @ sk_B) @ X0)
% 0.43/0.61          | ((sk_B) = (X0))
% 0.43/0.61          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['4', '7'])).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (((m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.43/0.61         (u1_struct_0 @ sk_A))
% 0.43/0.61        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('eq_fact', [status(thm)], ['8'])).
% 0.43/0.61  thf(t44_yellow_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.43/0.61         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.43/0.61          | (r1_orders_2 @ X19 @ (k3_yellow_0 @ X19) @ X18)
% 0.43/0.61          | ~ (l1_orders_2 @ X19)
% 0.43/0.61          | ~ (v1_yellow_0 @ X19)
% 0.43/0.61          | ~ (v5_orders_2 @ X19)
% 0.43/0.61          | (v2_struct_0 @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v5_orders_2 @ sk_A)
% 0.43/0.61        | ~ (v1_yellow_0 @ sk_A)
% 0.43/0.61        | ~ (l1_orders_2 @ sk_A)
% 0.43/0.61        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.43/0.61           (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.43/0.61  thf('12', plain, ((v5_orders_2 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('13', plain, ((v1_yellow_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('14', plain, ((l1_orders_2 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.43/0.61           (sk_C @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.43/0.61  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.43/0.61         (sk_C @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.43/0.61        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['15', '16'])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.43/0.61         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.43/0.61         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(d20_waybel_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( l1_orders_2 @ A ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.43/0.61             ( ![C:$i]:
% 0.43/0.61               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61                 ( ![D:$i]:
% 0.43/0.61                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.43/0.61                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.43/0.61          | ~ (v13_waybel_0 @ X20 @ X21)
% 0.43/0.61          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.43/0.61          | (r2_hidden @ X22 @ X20)
% 0.43/0.61          | ~ (r1_orders_2 @ X21 @ X23 @ X22)
% 0.43/0.61          | ~ (r2_hidden @ X23 @ X20)
% 0.43/0.61          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.43/0.61          | ~ (l1_orders_2 @ X21))),
% 0.43/0.61      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.43/0.61  thf('23', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (l1_orders_2 @ sk_A)
% 0.43/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | ~ (r2_hidden @ X0 @ sk_B)
% 0.43/0.61          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.43/0.61          | (r2_hidden @ X1 @ sk_B)
% 0.43/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.43/0.61  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('25', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61          | ~ (r2_hidden @ X0 @ sk_B)
% 0.43/0.61          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.43/0.61          | (r2_hidden @ X1 @ sk_B)
% 0.43/0.61          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.43/0.61  thf('27', plain,
% 0.43/0.61      ((![X0 : $i]:
% 0.43/0.61          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61           | (r2_hidden @ X0 @ sk_B)
% 0.43/0.61           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.43/0.61           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.43/0.61         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['20', '26'])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.43/0.61         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      ((![X0 : $i]:
% 0.43/0.61          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61           | (r2_hidden @ X0 @ sk_B)
% 0.43/0.61           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.43/0.61         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('demod', [status(thm)], ['27', '28'])).
% 0.43/0.61  thf('30', plain,
% 0.43/0.61      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.43/0.61         | (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.43/0.61         | ~ (m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.43/0.61              (u1_struct_0 @ sk_A))))
% 0.43/0.61         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['17', '29'])).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      (((m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.43/0.61         (u1_struct_0 @ sk_A))
% 0.43/0.61        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('eq_fact', [status(thm)], ['8'])).
% 0.43/0.61  thf(t2_subset, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ A @ B ) =>
% 0.43/0.61       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.43/0.61  thf('32', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         ((r2_hidden @ X9 @ X10)
% 0.43/0.61          | (v1_xboole_0 @ X10)
% 0.43/0.61          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [t2_subset])).
% 0.43/0.61  thf('33', plain,
% 0.43/0.61      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.43/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.43/0.61           (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(cc1_subset_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_xboole_0 @ A ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.43/0.61  thf('35', plain,
% 0.43/0.61      (![X5 : $i, X6 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.43/0.61          | (v1_xboole_0 @ X5)
% 0.43/0.61          | ~ (v1_xboole_0 @ X6))),
% 0.43/0.61      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.43/0.61  thf('36', plain,
% 0.43/0.61      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.43/0.61  thf('37', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('38', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['36', '37'])).
% 0.43/0.61  thf('39', plain,
% 0.43/0.61      (((r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.43/0.61         (u1_struct_0 @ sk_A))
% 0.43/0.61        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('clc', [status(thm)], ['33', '38'])).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((X1) = (X0))
% 0.43/0.61          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.43/0.61          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [t2_tarski])).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.43/0.61        | ~ (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.43/0.61        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      ((~ (r2_hidden @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 0.43/0.61        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['41'])).
% 0.43/0.61  thf('43', plain,
% 0.43/0.61      (((~ (m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.43/0.61            (u1_struct_0 @ sk_A))
% 0.43/0.61         | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.43/0.61         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('clc', [status(thm)], ['30', '42'])).
% 0.43/0.61  thf('44', plain,
% 0.43/0.61      (((m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.43/0.61         (u1_struct_0 @ sk_A))
% 0.43/0.61        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('eq_fact', [status(thm)], ['8'])).
% 0.43/0.61  thf('45', plain,
% 0.43/0.61      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.43/0.61         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('clc', [status(thm)], ['43', '44'])).
% 0.43/0.61  thf('46', plain,
% 0.43/0.61      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.43/0.61        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('47', plain,
% 0.43/0.61      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.43/0.61         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('split', [status(esa)], ['46'])).
% 0.43/0.61  thf('48', plain,
% 0.43/0.61      (((v1_subset_1 @ sk_B @ sk_B))
% 0.43/0.61         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.43/0.61             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['45', '47'])).
% 0.43/0.61  thf(d7_subset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.61       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.43/0.61  thf('49', plain,
% 0.43/0.61      (![X24 : $i, X25 : $i]:
% 0.43/0.61         (~ (v1_subset_1 @ X25 @ X24)
% 0.43/0.61          | ((X25) != (X24))
% 0.43/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.43/0.61  thf('50', plain,
% 0.43/0.61      (![X24 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X24))
% 0.43/0.61          | ~ (v1_subset_1 @ X24 @ X24))),
% 0.43/0.61      inference('simplify', [status(thm)], ['49'])).
% 0.43/0.61  thf(d10_xboole_0, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.61  thf('51', plain,
% 0.43/0.61      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.43/0.61  thf('52', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.43/0.61      inference('simplify', [status(thm)], ['51'])).
% 0.43/0.61  thf(t3_subset, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.43/0.61  thf('53', plain,
% 0.43/0.61      (![X11 : $i, X13 : $i]:
% 0.43/0.61         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.43/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.43/0.61  thf('54', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['52', '53'])).
% 0.43/0.61  thf('55', plain, (![X24 : $i]: ~ (v1_subset_1 @ X24 @ X24)),
% 0.43/0.61      inference('demod', [status(thm)], ['50', '54'])).
% 0.43/0.61  thf('56', plain,
% 0.43/0.61      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.43/0.61       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['48', '55'])).
% 0.43/0.61  thf('57', plain,
% 0.43/0.61      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.43/0.61       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('split', [status(esa)], ['46'])).
% 0.43/0.61  thf('58', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('59', plain,
% 0.43/0.61      (![X24 : $i, X25 : $i]:
% 0.43/0.61         (((X25) = (X24))
% 0.43/0.61          | (v1_subset_1 @ X25 @ X24)
% 0.43/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.43/0.61  thf('60', plain,
% 0.43/0.61      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['58', '59'])).
% 0.43/0.61  thf('61', plain,
% 0.43/0.61      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.43/0.61         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf('62', plain,
% 0.43/0.61      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.43/0.61         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['60', '61'])).
% 0.43/0.61  thf(dt_k3_yellow_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( l1_orders_2 @ A ) =>
% 0.43/0.61       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.43/0.61  thf('63', plain,
% 0.43/0.61      (![X17 : $i]:
% 0.43/0.61         ((m1_subset_1 @ (k3_yellow_0 @ X17) @ (u1_struct_0 @ X17))
% 0.43/0.61          | ~ (l1_orders_2 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.43/0.61  thf('64', plain,
% 0.43/0.61      ((((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B) | ~ (l1_orders_2 @ sk_A)))
% 0.43/0.61         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('sup+', [status(thm)], ['62', '63'])).
% 0.43/0.61  thf('65', plain, ((l1_orders_2 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('66', plain,
% 0.43/0.61      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.43/0.61         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('demod', [status(thm)], ['64', '65'])).
% 0.43/0.61  thf('67', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i]:
% 0.43/0.61         ((r2_hidden @ X9 @ X10)
% 0.43/0.61          | (v1_xboole_0 @ X10)
% 0.43/0.61          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [t2_subset])).
% 0.43/0.61  thf('68', plain,
% 0.43/0.61      ((((v1_xboole_0 @ sk_B) | (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.43/0.61         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.43/0.61  thf('69', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('70', plain,
% 0.43/0.61      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.43/0.61         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('clc', [status(thm)], ['68', '69'])).
% 0.43/0.61  thf('71', plain,
% 0.43/0.61      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.43/0.61         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.43/0.61      inference('split', [status(esa)], ['46'])).
% 0.43/0.61  thf('72', plain,
% 0.43/0.61      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.43/0.61       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.43/0.61  thf('73', plain, ($false),
% 0.43/0.61      inference('sat_resolution*', [status(thm)], ['1', '56', '57', '72'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
