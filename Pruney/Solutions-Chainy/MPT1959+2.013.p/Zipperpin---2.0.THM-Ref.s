%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ywsw7yjg1C

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:10 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 201 expanded)
%              Number of leaves         :   31 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :  894 (2804 expanded)
%              Number of equality atoms :   25 (  45 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( X13 = X11 )
      | ( m1_subset_1 @ ( sk_D @ X11 @ X13 @ X12 ) @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( r1_orders_2 @ X23 @ ( k3_yellow_0 @ X23 ) @ X22 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v1_yellow_0 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('14',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('27',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
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

thf('29',plain,(
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

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( X13 = X11 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X13 @ X12 ) @ X13 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X13 @ X12 ) @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('44',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['37','44'])).

thf('46',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('47',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['47','49'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('51',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_subset_1 @ X29 @ X28 )
      | ( X29 != X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('52',plain,(
    ! [X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( v1_subset_1 @ X28 @ X28 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('54',plain,(
    ! [X28: $i] :
      ~ ( v1_subset_1 @ X28 @ X28 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['48'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X29 = X28 )
      | ( v1_subset_1 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('59',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('62',plain,(
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('63',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

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
    inference(split,[status(esa)],['48'])).

thf('72',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','55','56','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ywsw7yjg1C
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 231 iterations in 0.129s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.40/0.58  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.40/0.58  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.40/0.58  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.40/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.58  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.40/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.40/0.58  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.40/0.58  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(t8_waybel_7, conjecture,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.40/0.58         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.40/0.58         ( l1_orders_2 @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.40/0.58             ( v13_waybel_0 @ B @ A ) & 
% 0.40/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.40/0.58           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.40/0.58             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i]:
% 0.40/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.40/0.58            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.40/0.58            ( l1_orders_2 @ A ) ) =>
% 0.40/0.58          ( ![B:$i]:
% 0.40/0.58            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.40/0.58                ( v13_waybel_0 @ B @ A ) & 
% 0.40/0.58                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.40/0.58              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.40/0.58                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.40/0.58        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.40/0.58       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('split', [status(esa)], ['0'])).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d10_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.58  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.40/0.58      inference('simplify', [status(thm)], ['3'])).
% 0.40/0.58  thf(d1_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.40/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.58         (~ (r1_tarski @ X3 @ X4)
% 0.40/0.58          | (r2_hidden @ X3 @ X5)
% 0.40/0.58          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (![X3 : $i, X4 : $i]:
% 0.40/0.58         ((r2_hidden @ X3 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X3 @ X4))),
% 0.40/0.58      inference('simplify', [status(thm)], ['5'])).
% 0.40/0.58  thf('7', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.40/0.58  thf(t1_subset, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X14 : $i, X15 : $i]:
% 0.40/0.58         ((m1_subset_1 @ X14 @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 0.40/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.40/0.58  thf('9', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.58  thf(t8_subset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58       ( ![C:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58           ( ( ![D:$i]:
% 0.40/0.58               ( ( m1_subset_1 @ D @ A ) =>
% 0.40/0.58                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.40/0.58             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.40/0.58          | ((X13) = (X11))
% 0.40/0.58          | (m1_subset_1 @ (sk_D @ X11 @ X13 @ X12) @ X12)
% 0.40/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.40/0.58          | (m1_subset_1 @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.40/0.58          | ((X1) = (X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.40/0.58        | (m1_subset_1 @ 
% 0.40/0.58           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.40/0.58           (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['2', '11'])).
% 0.40/0.58  thf(t44_yellow_0, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.40/0.58         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X22 : $i, X23 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.40/0.58          | (r1_orders_2 @ X23 @ (k3_yellow_0 @ X23) @ X22)
% 0.40/0.58          | ~ (l1_orders_2 @ X23)
% 0.40/0.58          | ~ (v1_yellow_0 @ X23)
% 0.40/0.58          | ~ (v5_orders_2 @ X23)
% 0.40/0.58          | (v2_struct_0 @ X23))),
% 0.40/0.58      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | ~ (v5_orders_2 @ sk_A)
% 0.40/0.58        | ~ (v1_yellow_0 @ sk_A)
% 0.40/0.58        | ~ (l1_orders_2 @ sk_A)
% 0.40/0.58        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.40/0.58           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.58  thf('15', plain, ((v5_orders_2 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('16', plain, ((v1_yellow_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.40/0.58        | (v2_struct_0 @ sk_A)
% 0.40/0.58        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.40/0.58           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.40/0.58  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.40/0.58         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.40/0.58        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('clc', [status(thm)], ['18', '19'])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.40/0.58         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('split', [status(esa)], ['0'])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(l3_subset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X8 @ X9)
% 0.40/0.58          | (r2_hidden @ X8 @ X10)
% 0.40/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.40/0.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.40/0.58         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['21', '24'])).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (![X14 : $i, X15 : $i]:
% 0.40/0.58         ((m1_subset_1 @ X14 @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 0.40/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.40/0.58         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d20_waybel_0, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( l1_orders_2 @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.58           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.40/0.58             ( ![C:$i]:
% 0.40/0.58               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58                 ( ![D:$i]:
% 0.40/0.58                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.40/0.58                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.40/0.58                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.40/0.58          | ~ (v13_waybel_0 @ X24 @ X25)
% 0.40/0.58          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.40/0.58          | (r2_hidden @ X26 @ X24)
% 0.40/0.58          | ~ (r1_orders_2 @ X25 @ X27 @ X26)
% 0.40/0.58          | ~ (r2_hidden @ X27 @ X24)
% 0.40/0.58          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.40/0.58          | ~ (l1_orders_2 @ X25))),
% 0.40/0.58      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (l1_orders_2 @ sk_A)
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.58          | ~ (r2_hidden @ X0 @ sk_B)
% 0.40/0.58          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.40/0.58          | (r2_hidden @ X1 @ sk_B)
% 0.40/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.40/0.58          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.40/0.58  thf('31', plain, ((l1_orders_2 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('32', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.58          | ~ (r2_hidden @ X0 @ sk_B)
% 0.40/0.58          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.40/0.58          | (r2_hidden @ X1 @ sk_B)
% 0.40/0.58          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      ((![X0 : $i]:
% 0.40/0.58          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.58           | (r2_hidden @ X0 @ sk_B)
% 0.40/0.58           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.40/0.58           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.40/0.58         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['27', '33'])).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.40/0.58         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('split', [status(esa)], ['0'])).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      ((![X0 : $i]:
% 0.40/0.58          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.40/0.58           | (r2_hidden @ X0 @ sk_B)
% 0.40/0.58           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.40/0.58         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.40/0.58         | (r2_hidden @ 
% 0.40/0.58            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.40/0.58         | ~ (m1_subset_1 @ 
% 0.40/0.58              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.40/0.58              (u1_struct_0 @ sk_A))))
% 0.40/0.58         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['20', '36'])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('39', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.40/0.58          | ((X13) = (X11))
% 0.40/0.58          | ~ (r2_hidden @ (sk_D @ X11 @ X13 @ X12) @ X13)
% 0.40/0.58          | ~ (r2_hidden @ (sk_D @ X11 @ X13 @ X12) @ X11)
% 0.40/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.40/0.58          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.40/0.58          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.40/0.58          | ((X1) = (X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.40/0.58  thf('42', plain,
% 0.40/0.58      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.40/0.58        | ~ (r2_hidden @ 
% 0.40/0.58             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.40/0.58        | ~ (r2_hidden @ 
% 0.40/0.58             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.40/0.58             (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['38', '41'])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      ((~ (r2_hidden @ 
% 0.40/0.58           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.40/0.58        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('clc', [status(thm)], ['42', '43'])).
% 0.40/0.58  thf('45', plain,
% 0.40/0.58      (((~ (m1_subset_1 @ 
% 0.40/0.58            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.40/0.58            (u1_struct_0 @ sk_A))
% 0.40/0.58         | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.40/0.58         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('clc', [status(thm)], ['37', '44'])).
% 0.40/0.58  thf('46', plain,
% 0.40/0.58      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.40/0.58        | (m1_subset_1 @ 
% 0.40/0.58           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.40/0.58           (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['2', '11'])).
% 0.40/0.58  thf('47', plain,
% 0.40/0.58      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.40/0.58         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('clc', [status(thm)], ['45', '46'])).
% 0.40/0.58  thf('48', plain,
% 0.40/0.58      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.40/0.58        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('49', plain,
% 0.40/0.58      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.40/0.58         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('split', [status(esa)], ['48'])).
% 0.40/0.58  thf('50', plain,
% 0.40/0.58      (((v1_subset_1 @ sk_B @ sk_B))
% 0.40/0.58         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.40/0.58             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['47', '49'])).
% 0.40/0.58  thf(d7_subset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.40/0.58  thf('51', plain,
% 0.40/0.58      (![X28 : $i, X29 : $i]:
% 0.40/0.58         (~ (v1_subset_1 @ X29 @ X28)
% 0.40/0.58          | ((X29) != (X28))
% 0.40/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.40/0.58  thf('52', plain,
% 0.40/0.58      (![X28 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X28))
% 0.40/0.58          | ~ (v1_subset_1 @ X28 @ X28))),
% 0.40/0.58      inference('simplify', [status(thm)], ['51'])).
% 0.40/0.58  thf('53', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.58  thf('54', plain, (![X28 : $i]: ~ (v1_subset_1 @ X28 @ X28)),
% 0.40/0.58      inference('demod', [status(thm)], ['52', '53'])).
% 0.40/0.58  thf('55', plain,
% 0.40/0.58      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.40/0.58       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['50', '54'])).
% 0.40/0.58  thf('56', plain,
% 0.40/0.58      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.40/0.58       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('split', [status(esa)], ['48'])).
% 0.40/0.58  thf('57', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('58', plain,
% 0.40/0.58      (![X28 : $i, X29 : $i]:
% 0.40/0.58         (((X29) = (X28))
% 0.40/0.58          | (v1_subset_1 @ X29 @ X28)
% 0.40/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.40/0.58  thf('59', plain,
% 0.40/0.58      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.40/0.58        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.40/0.58  thf('60', plain,
% 0.40/0.58      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('split', [status(esa)], ['0'])).
% 0.40/0.58  thf('61', plain,
% 0.40/0.58      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.40/0.58  thf(dt_k3_yellow_0, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( l1_orders_2 @ A ) =>
% 0.40/0.58       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.40/0.58  thf('62', plain,
% 0.40/0.58      (![X21 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k3_yellow_0 @ X21) @ (u1_struct_0 @ X21))
% 0.40/0.58          | ~ (l1_orders_2 @ X21))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.40/0.58  thf(t2_subset, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ A @ B ) =>
% 0.40/0.58       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.40/0.58  thf('63', plain,
% 0.40/0.58      (![X16 : $i, X17 : $i]:
% 0.40/0.58         ((r2_hidden @ X16 @ X17)
% 0.40/0.58          | (v1_xboole_0 @ X17)
% 0.40/0.58          | ~ (m1_subset_1 @ X16 @ X17))),
% 0.40/0.58      inference('cnf', [status(esa)], [t2_subset])).
% 0.40/0.58  thf('64', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (l1_orders_2 @ X0)
% 0.40/0.58          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.40/0.58          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['62', '63'])).
% 0.40/0.58  thf('65', plain,
% 0.40/0.58      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.40/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.40/0.58         | ~ (l1_orders_2 @ sk_A)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['61', '64'])).
% 0.40/0.58  thf('66', plain,
% 0.40/0.58      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.40/0.58  thf('67', plain, ((l1_orders_2 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('68', plain,
% 0.40/0.58      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B) | (v1_xboole_0 @ sk_B)))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.40/0.58  thf('69', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('70', plain,
% 0.40/0.58      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.40/0.58         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.40/0.58      inference('clc', [status(thm)], ['68', '69'])).
% 0.40/0.58  thf('71', plain,
% 0.40/0.58      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.40/0.58         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('split', [status(esa)], ['48'])).
% 0.40/0.58  thf('72', plain,
% 0.40/0.58      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.40/0.58       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['70', '71'])).
% 0.40/0.58  thf('73', plain, ($false),
% 0.40/0.58      inference('sat_resolution*', [status(thm)], ['1', '55', '56', '72'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
