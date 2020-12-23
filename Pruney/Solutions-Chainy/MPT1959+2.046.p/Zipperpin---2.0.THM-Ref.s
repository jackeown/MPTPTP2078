%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cfHQgc4u7O

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:16 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 264 expanded)
%              Number of leaves         :   31 (  90 expanded)
%              Depth                    :   18
%              Number of atoms          :  951 (3618 expanded)
%              Number of equality atoms :   24 (  43 expanded)
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

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( X9 = X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X9 )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( X9 = X7 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X9 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','22'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('25',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( r1_orders_2 @ X22 @ ( k3_yellow_0 @ X22 ) @ X21 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v1_yellow_0 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('27',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('36',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v13_waybel_0 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( r2_hidden @ X25 @ X23 )
      | ~ ( r1_orders_2 @ X24 @ X26 @ X25 )
      | ~ ( r2_hidden @ X26 @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','21'])).

thf('50',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('52',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['52','54'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('56',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_subset_1 @ X28 @ X27 )
      | ( X28 != X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('57',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( v1_subset_1 @ X27 @ X27 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('59',plain,(
    ! [X27: $i] :
      ~ ( v1_subset_1 @ X27 @ X27 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['53'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X28 = X27 )
      | ( v1_subset_1 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('64',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('67',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X20 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('68',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('72',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['53'])).

thf('77',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','60','61','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cfHQgc4u7O
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 233 iterations in 0.204s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.45/0.67  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.45/0.67  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.45/0.67  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.45/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.45/0.67  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.67  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.45/0.67  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.45/0.67  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.45/0.67  thf(t8_waybel_7, conjecture,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.67         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.45/0.67         ( l1_orders_2 @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.45/0.67             ( v13_waybel_0 @ B @ A ) & 
% 0.45/0.67             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.67           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.45/0.67             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i]:
% 0.45/0.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.67            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.45/0.67            ( l1_orders_2 @ A ) ) =>
% 0.45/0.67          ( ![B:$i]:
% 0.45/0.67            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.45/0.67                ( v13_waybel_0 @ B @ A ) & 
% 0.45/0.67                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.67              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.45/0.67                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.45/0.67        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.45/0.67       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('split', [status(esa)], ['0'])).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(d3_tarski, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (![X1 : $i, X3 : $i]:
% 0.45/0.67         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      (![X1 : $i, X3 : $i]:
% 0.45/0.67         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.67  thf('6', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.45/0.67      inference('simplify', [status(thm)], ['5'])).
% 0.45/0.67  thf(t3_subset, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X14 : $i, X16 : $i]:
% 0.45/0.67         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.67  thf('8', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.67  thf(t8_subset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.67       ( ![C:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.67           ( ( ![D:$i]:
% 0.45/0.67               ( ( m1_subset_1 @ D @ A ) =>
% 0.45/0.67                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.45/0.67             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.45/0.67          | ((X9) = (X7))
% 0.45/0.67          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X9)
% 0.45/0.67          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X7)
% 0.45/0.67          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.45/0.67          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.45/0.67          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.45/0.67          | ((X1) = (X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.45/0.67        | (r2_hidden @ 
% 0.45/0.67           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.45/0.67        | (r2_hidden @ 
% 0.45/0.67           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.67           (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['2', '10'])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('13', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.45/0.67          | ((X9) = (X7))
% 0.45/0.67          | ~ (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X9)
% 0.45/0.67          | ~ (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X7)
% 0.45/0.67          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.45/0.67          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.45/0.67          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.45/0.67          | ((X1) = (X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.45/0.67        | ~ (r2_hidden @ 
% 0.45/0.67             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.45/0.67        | ~ (r2_hidden @ 
% 0.45/0.67             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.67             (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['12', '15'])).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X14 : $i, X15 : $i]:
% 0.45/0.67         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.67  thf('19', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.67          | (r2_hidden @ X0 @ X2)
% 0.45/0.67          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      ((~ (r2_hidden @ 
% 0.45/0.67           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.45/0.67        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('clc', [status(thm)], ['16', '21'])).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      (((r2_hidden @ 
% 0.45/0.67         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.67         (u1_struct_0 @ sk_A))
% 0.45/0.67        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('clc', [status(thm)], ['11', '22'])).
% 0.45/0.67  thf(t1_subset, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (![X10 : $i, X11 : $i]:
% 0.45/0.67         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.45/0.67      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.45/0.67        | (m1_subset_1 @ 
% 0.45/0.67           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.67           (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.67  thf(t44_yellow_0, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.45/0.67         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.67           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (![X21 : $i, X22 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.45/0.67          | (r1_orders_2 @ X22 @ (k3_yellow_0 @ X22) @ X21)
% 0.45/0.67          | ~ (l1_orders_2 @ X22)
% 0.45/0.67          | ~ (v1_yellow_0 @ X22)
% 0.45/0.67          | ~ (v5_orders_2 @ X22)
% 0.45/0.67          | (v2_struct_0 @ X22))),
% 0.45/0.67      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.45/0.67        | (v2_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v5_orders_2 @ sk_A)
% 0.45/0.67        | ~ (v1_yellow_0 @ sk_A)
% 0.45/0.67        | ~ (l1_orders_2 @ sk_A)
% 0.45/0.67        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.45/0.67           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.67  thf('28', plain, ((v5_orders_2 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('29', plain, ((v1_yellow_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.45/0.67        | (v2_struct_0 @ sk_A)
% 0.45/0.67        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.45/0.67           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.45/0.67  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.45/0.67         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.45/0.67        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('clc', [status(thm)], ['31', '32'])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.45/0.67         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.67      inference('split', [status(esa)], ['0'])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.45/0.67         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      (![X10 : $i, X11 : $i]:
% 0.45/0.67         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.45/0.67      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.45/0.67         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(d20_waybel_0, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_orders_2 @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.67           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.45/0.67             ( ![C:$i]:
% 0.45/0.67               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.67                 ( ![D:$i]:
% 0.45/0.67                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.67                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.45/0.67                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.45/0.67          | ~ (v13_waybel_0 @ X23 @ X24)
% 0.45/0.67          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.45/0.67          | (r2_hidden @ X25 @ X23)
% 0.45/0.67          | ~ (r1_orders_2 @ X24 @ X26 @ X25)
% 0.45/0.67          | ~ (r2_hidden @ X26 @ X23)
% 0.45/0.67          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 0.45/0.67          | ~ (l1_orders_2 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.45/0.67  thf('41', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (l1_orders_2 @ sk_A)
% 0.45/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.67          | ~ (r2_hidden @ X0 @ sk_B)
% 0.45/0.67          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.45/0.67          | (r2_hidden @ X1 @ sk_B)
% 0.45/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.45/0.67          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.67  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('43', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('44', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.67          | ~ (r2_hidden @ X0 @ sk_B)
% 0.45/0.67          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.45/0.67          | (r2_hidden @ X1 @ sk_B)
% 0.45/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.45/0.67  thf('45', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.67           | (r2_hidden @ X0 @ sk_B)
% 0.45/0.67           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.45/0.67           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.45/0.67         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['38', '44'])).
% 0.45/0.67  thf('46', plain,
% 0.45/0.67      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.45/0.67         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.67      inference('split', [status(esa)], ['0'])).
% 0.45/0.67  thf('47', plain,
% 0.45/0.67      ((![X0 : $i]:
% 0.45/0.67          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.67           | (r2_hidden @ X0 @ sk_B)
% 0.45/0.67           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.45/0.67         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.67      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.67  thf('48', plain,
% 0.45/0.67      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.45/0.67         | (r2_hidden @ 
% 0.45/0.67            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.45/0.67         | ~ (m1_subset_1 @ 
% 0.45/0.67              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.67              (u1_struct_0 @ sk_A))))
% 0.45/0.67         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['33', '47'])).
% 0.45/0.67  thf('49', plain,
% 0.45/0.67      ((~ (r2_hidden @ 
% 0.45/0.67           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.45/0.67        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('clc', [status(thm)], ['16', '21'])).
% 0.45/0.67  thf('50', plain,
% 0.45/0.67      (((~ (m1_subset_1 @ 
% 0.45/0.67            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.67            (u1_struct_0 @ sk_A))
% 0.45/0.67         | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.45/0.67         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['48', '49'])).
% 0.45/0.67  thf('51', plain,
% 0.45/0.67      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.45/0.67        | (m1_subset_1 @ 
% 0.45/0.67           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.67           (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.67  thf('52', plain,
% 0.45/0.67      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.45/0.67         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.67      inference('clc', [status(thm)], ['50', '51'])).
% 0.45/0.67  thf('53', plain,
% 0.45/0.67      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.45/0.67        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('54', plain,
% 0.45/0.67      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.45/0.67         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('split', [status(esa)], ['53'])).
% 0.45/0.67  thf('55', plain,
% 0.45/0.67      (((v1_subset_1 @ sk_B @ sk_B))
% 0.45/0.67         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.45/0.67             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['52', '54'])).
% 0.45/0.67  thf(d7_subset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.67       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.45/0.67  thf('56', plain,
% 0.45/0.67      (![X27 : $i, X28 : $i]:
% 0.45/0.67         (~ (v1_subset_1 @ X28 @ X27)
% 0.45/0.67          | ((X28) != (X27))
% 0.45/0.67          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.45/0.67  thf('57', plain,
% 0.45/0.67      (![X27 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X27))
% 0.45/0.67          | ~ (v1_subset_1 @ X27 @ X27))),
% 0.45/0.67      inference('simplify', [status(thm)], ['56'])).
% 0.45/0.67  thf('58', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.67  thf('59', plain, (![X27 : $i]: ~ (v1_subset_1 @ X27 @ X27)),
% 0.45/0.67      inference('demod', [status(thm)], ['57', '58'])).
% 0.45/0.67  thf('60', plain,
% 0.45/0.67      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.45/0.67       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['55', '59'])).
% 0.45/0.67  thf('61', plain,
% 0.45/0.67      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.45/0.67       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('split', [status(esa)], ['53'])).
% 0.45/0.67  thf('62', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('63', plain,
% 0.45/0.67      (![X27 : $i, X28 : $i]:
% 0.45/0.67         (((X28) = (X27))
% 0.45/0.67          | (v1_subset_1 @ X28 @ X27)
% 0.45/0.67          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.45/0.67  thf('64', plain,
% 0.45/0.67      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.45/0.67        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.67  thf('65', plain,
% 0.45/0.67      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.45/0.67         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('split', [status(esa)], ['0'])).
% 0.45/0.67  thf('66', plain,
% 0.45/0.67      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.45/0.67         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.67  thf(dt_k3_yellow_0, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_orders_2 @ A ) =>
% 0.45/0.67       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.45/0.67  thf('67', plain,
% 0.45/0.67      (![X20 : $i]:
% 0.45/0.67         ((m1_subset_1 @ (k3_yellow_0 @ X20) @ (u1_struct_0 @ X20))
% 0.45/0.67          | ~ (l1_orders_2 @ X20))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.45/0.67  thf(t2_subset, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.67       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.67  thf('68', plain,
% 0.45/0.67      (![X12 : $i, X13 : $i]:
% 0.45/0.67         ((r2_hidden @ X12 @ X13)
% 0.45/0.67          | (v1_xboole_0 @ X13)
% 0.45/0.67          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.45/0.67      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.67  thf('69', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (l1_orders_2 @ X0)
% 0.45/0.67          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.67          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['67', '68'])).
% 0.45/0.67  thf('70', plain,
% 0.45/0.67      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.45/0.67         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.67         | ~ (l1_orders_2 @ sk_A)))
% 0.45/0.67         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['66', '69'])).
% 0.45/0.67  thf('71', plain,
% 0.45/0.67      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.45/0.67         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.67  thf('72', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('73', plain,
% 0.45/0.67      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B) | (v1_xboole_0 @ sk_B)))
% 0.45/0.67         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.45/0.67  thf('74', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('75', plain,
% 0.45/0.67      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.45/0.67         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.67      inference('clc', [status(thm)], ['73', '74'])).
% 0.45/0.67  thf('76', plain,
% 0.45/0.67      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.45/0.67         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.67      inference('split', [status(esa)], ['53'])).
% 0.45/0.67  thf('77', plain,
% 0.45/0.67      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.45/0.67       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['75', '76'])).
% 0.45/0.67  thf('78', plain, ($false),
% 0.45/0.67      inference('sat_resolution*', [status(thm)], ['1', '60', '61', '77'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
