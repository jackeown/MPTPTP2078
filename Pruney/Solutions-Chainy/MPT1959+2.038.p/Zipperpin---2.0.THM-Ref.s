%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X8CQaqSyQH

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:14 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 216 expanded)
%              Number of leaves         :   39 (  79 expanded)
%              Depth                    :   24
%              Number of atoms          : 1148 (3489 expanded)
%              Number of equality atoms :   44 (  51 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

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

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( ( k3_yellow_0 @ X9 )
        = ( k1_yellow_0 @ X9 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X1 @ X2 ) @ X2 )
      | ( X2 = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('5',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

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

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( ( k1_yellow_0 @ X20 @ ( k5_waybel_0 @ X20 @ X19 ) )
        = X19 )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('7',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(t42_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( r1_yellow_0 @ A @ k1_xboole_0 )
        & ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X14: $i] :
      ( ( r1_yellow_0 @ X14 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v1_yellow_0 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('17',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( r1_yellow_0 @ X20 @ ( k5_waybel_0 @ X20 @ X19 ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('19',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(t34_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( ( r1_tarski @ B @ C )
            & ( r1_yellow_0 @ A @ B )
            & ( r1_yellow_0 @ A @ C ) )
         => ( r1_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_orders_2 @ X11 @ ( k1_yellow_0 @ X11 @ X12 ) @ ( k1_yellow_0 @ X11 @ X13 ) )
      | ~ ( r1_yellow_0 @ X11 @ X13 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_yellow_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t34_yellow_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','31'])).

thf('33',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['14','38'])).

thf('40',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['2','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
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

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v13_waybel_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ X17 @ X15 )
      | ~ ( r1_orders_2 @ X16 @ X18 @ X17 )
      | ~ ( r2_hidden @ X18 @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','57'])).

thf('59',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('60',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ X1 )
      | ( X2 = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('62',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['65','67'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('69',plain,(
    ! [X3: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X3 ) @ X3 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('70',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( sk_B @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('71',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22 = X21 )
      | ( v1_subset_1 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X3: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X3 ) @ X3 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X3: $i] :
      ~ ( v1_subset_1 @ X3 @ X3 ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['66'])).

thf('78',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22 = X21 )
      | ( v1_subset_1 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('80',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('83',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('84',plain,
    ( ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('87',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('88',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['66'])).

thf('92',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','76','77','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X8CQaqSyQH
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 300 iterations in 0.149s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.62  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.44/0.62  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.44/0.62  thf(k5_waybel_0_type, type, k5_waybel_0: $i > $i > $i).
% 0.44/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.62  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.44/0.62  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.44/0.62  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.44/0.62  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.44/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.62  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.44/0.62  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.44/0.62  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.44/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.62  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.44/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.44/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.62  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.44/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.44/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.62  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.44/0.62  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.44/0.62  thf(t8_waybel_7, conjecture,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.44/0.62         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.44/0.62         ( l1_orders_2 @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.44/0.62             ( v13_waybel_0 @ B @ A ) & 
% 0.44/0.62             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.62           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.44/0.62             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i]:
% 0.44/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.44/0.62            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.44/0.62            ( l1_orders_2 @ A ) ) =>
% 0.44/0.62          ( ![B:$i]:
% 0.44/0.62            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.44/0.62                ( v13_waybel_0 @ B @ A ) & 
% 0.44/0.62                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.62              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.44/0.62                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.44/0.62  thf('0', plain,
% 0.44/0.62      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.44/0.62        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('1', plain,
% 0.44/0.62      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.44/0.62       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('split', [status(esa)], ['0'])).
% 0.44/0.62  thf(d11_yellow_0, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_orders_2 @ A ) =>
% 0.44/0.62       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      (![X9 : $i]:
% 0.44/0.62         (((k3_yellow_0 @ X9) = (k1_yellow_0 @ X9 @ k1_xboole_0))
% 0.44/0.62          | ~ (l1_orders_2 @ X9))),
% 0.44/0.62      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t49_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.62       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.44/0.62         ( ( A ) = ( B ) ) ) ))).
% 0.44/0.62  thf('4', plain,
% 0.44/0.62      (![X1 : $i, X2 : $i]:
% 0.44/0.62         ((m1_subset_1 @ (sk_C @ X1 @ X2) @ X2)
% 0.44/0.62          | ((X2) = (X1))
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.44/0.62  thf('5', plain,
% 0.44/0.62      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62           (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.62  thf(t34_waybel_0, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.44/0.62         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62           ( ( r1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) ) & 
% 0.44/0.62             ( ( k1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      (![X19 : $i, X20 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.44/0.62          | ((k1_yellow_0 @ X20 @ (k5_waybel_0 @ X20 @ X19)) = (X19))
% 0.44/0.62          | ~ (l1_orders_2 @ X20)
% 0.44/0.62          | ~ (v5_orders_2 @ X20)
% 0.44/0.62          | ~ (v4_orders_2 @ X20)
% 0.44/0.62          | ~ (v3_orders_2 @ X20)
% 0.44/0.62          | (v2_struct_0 @ X20))),
% 0.44/0.62      inference('cnf', [status(esa)], [t34_waybel_0])).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62        | (v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (v3_orders_2 @ sk_A)
% 0.44/0.62        | ~ (v4_orders_2 @ sk_A)
% 0.44/0.62        | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62        | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62        | ((k1_yellow_0 @ sk_A @ 
% 0.44/0.62            (k5_waybel_0 @ sk_A @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.44/0.62            = (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.62  thf('8', plain, ((v3_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('9', plain, ((v4_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('10', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62        | (v2_struct_0 @ sk_A)
% 0.44/0.62        | ((k1_yellow_0 @ sk_A @ 
% 0.44/0.62            (k5_waybel_0 @ sk_A @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.44/0.62            = (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.44/0.62  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      ((((k1_yellow_0 @ sk_A @ 
% 0.44/0.62          (k5_waybel_0 @ sk_A @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.44/0.62          = (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.44/0.62      inference('clc', [status(thm)], ['12', '13'])).
% 0.44/0.62  thf(t42_yellow_0, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.44/0.62         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.44/0.62       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 0.44/0.62         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 0.44/0.62  thf('15', plain,
% 0.44/0.62      (![X14 : $i]:
% 0.44/0.62         ((r1_yellow_0 @ X14 @ k1_xboole_0)
% 0.44/0.62          | ~ (l1_orders_2 @ X14)
% 0.44/0.62          | ~ (v1_yellow_0 @ X14)
% 0.44/0.62          | ~ (v5_orders_2 @ X14)
% 0.44/0.62          | (v2_struct_0 @ X14))),
% 0.44/0.62      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.44/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.62  thf('16', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.44/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62           (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      (![X19 : $i, X20 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.44/0.62          | (r1_yellow_0 @ X20 @ (k5_waybel_0 @ X20 @ X19))
% 0.44/0.62          | ~ (l1_orders_2 @ X20)
% 0.44/0.62          | ~ (v5_orders_2 @ X20)
% 0.44/0.62          | ~ (v4_orders_2 @ X20)
% 0.44/0.62          | ~ (v3_orders_2 @ X20)
% 0.44/0.62          | (v2_struct_0 @ X20))),
% 0.44/0.62      inference('cnf', [status(esa)], [t34_waybel_0])).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62        | (v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (v3_orders_2 @ sk_A)
% 0.44/0.62        | ~ (v4_orders_2 @ sk_A)
% 0.44/0.62        | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62        | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62        | (r1_yellow_0 @ sk_A @ 
% 0.44/0.62           (k5_waybel_0 @ sk_A @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.62  thf('20', plain, ((v3_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('21', plain, ((v4_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('22', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('24', plain,
% 0.44/0.62      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62        | (v2_struct_0 @ sk_A)
% 0.44/0.62        | (r1_yellow_0 @ sk_A @ 
% 0.44/0.62           (k5_waybel_0 @ sk_A @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))))),
% 0.44/0.62      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.44/0.62  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('26', plain,
% 0.44/0.62      (((r1_yellow_0 @ sk_A @ 
% 0.44/0.62         (k5_waybel_0 @ sk_A @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.44/0.62        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.44/0.62      inference('clc', [status(thm)], ['24', '25'])).
% 0.44/0.62  thf(t34_yellow_0, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_orders_2 @ A ) =>
% 0.44/0.62       ( ![B:$i,C:$i]:
% 0.44/0.62         ( ( ( r1_tarski @ B @ C ) & ( r1_yellow_0 @ A @ B ) & 
% 0.44/0.62             ( r1_yellow_0 @ A @ C ) ) =>
% 0.44/0.62           ( r1_orders_2 @
% 0.44/0.62             A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) ))).
% 0.44/0.62  thf('27', plain,
% 0.44/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.62         ((r1_orders_2 @ X11 @ (k1_yellow_0 @ X11 @ X12) @ 
% 0.44/0.62           (k1_yellow_0 @ X11 @ X13))
% 0.44/0.62          | ~ (r1_yellow_0 @ X11 @ X13)
% 0.44/0.62          | ~ (r1_tarski @ X12 @ X13)
% 0.44/0.62          | ~ (r1_yellow_0 @ X11 @ X12)
% 0.44/0.62          | ~ (l1_orders_2 @ X11))),
% 0.44/0.62      inference('cnf', [status(esa)], [t34_yellow_0])).
% 0.44/0.62  thf('28', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62          | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62          | ~ (r1_yellow_0 @ sk_A @ X0)
% 0.44/0.62          | ~ (r1_tarski @ X0 @ 
% 0.44/0.62               (k5_waybel_0 @ sk_A @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.44/0.62          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.44/0.62             (k1_yellow_0 @ sk_A @ 
% 0.44/0.62              (k5_waybel_0 @ sk_A @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.62  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('30', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62          | ~ (r1_yellow_0 @ sk_A @ X0)
% 0.44/0.62          | ~ (r1_tarski @ X0 @ 
% 0.44/0.62               (k5_waybel_0 @ sk_A @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.44/0.62          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.44/0.62             (k1_yellow_0 @ sk_A @ 
% 0.44/0.62              (k5_waybel_0 @ sk_A @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))))),
% 0.44/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.62  thf('31', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.44/0.62         (k1_yellow_0 @ sk_A @ 
% 0.44/0.62          (k5_waybel_0 @ sk_A @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))))
% 0.44/0.62        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 0.44/0.62        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['16', '30'])).
% 0.44/0.62  thf('32', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | ~ (v5_orders_2 @ sk_A)
% 0.44/0.62        | ~ (v1_yellow_0 @ sk_A)
% 0.44/0.62        | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62        | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.44/0.62           (k1_yellow_0 @ sk_A @ 
% 0.44/0.62            (k5_waybel_0 @ sk_A @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['15', '31'])).
% 0.44/0.62  thf('33', plain, ((v5_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('34', plain, ((v1_yellow_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('36', plain,
% 0.44/0.62      (((v2_struct_0 @ sk_A)
% 0.44/0.62        | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.44/0.62           (k1_yellow_0 @ sk_A @ 
% 0.44/0.62            (k5_waybel_0 @ sk_A @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))))),
% 0.44/0.62      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.44/0.62  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('38', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.44/0.62         (k1_yellow_0 @ sk_A @ 
% 0.44/0.62          (k5_waybel_0 @ sk_A @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))))
% 0.44/0.62        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.44/0.62      inference('clc', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf('39', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.44/0.62         (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62        | ((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['14', '38'])).
% 0.44/0.62  thf('40', plain,
% 0.44/0.62      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.44/0.62           (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('simplify', [status(thm)], ['39'])).
% 0.44/0.62  thf('41', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.44/0.62         (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62        | ~ (l1_orders_2 @ sk_A)
% 0.44/0.62        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['2', '40'])).
% 0.44/0.62  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.44/0.62         (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 0.44/0.62      inference('demod', [status(thm)], ['41', '42'])).
% 0.44/0.62  thf('44', plain,
% 0.44/0.62      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.44/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('split', [status(esa)], ['0'])).
% 0.44/0.62  thf('45', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t4_subset, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.44/0.62       ( m1_subset_1 @ A @ C ) ))).
% 0.44/0.62  thf('46', plain,
% 0.44/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X6 @ X7)
% 0.44/0.62          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.44/0.62          | (m1_subset_1 @ X6 @ X8))),
% 0.44/0.62      inference('cnf', [status(esa)], [t4_subset])).
% 0.44/0.62  thf('47', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.44/0.62  thf('48', plain,
% 0.44/0.62      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.44/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['44', '47'])).
% 0.44/0.62  thf('49', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(d20_waybel_0, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_orders_2 @ A ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.44/0.62             ( ![C:$i]:
% 0.44/0.62               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62                 ( ![D:$i]:
% 0.44/0.62                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.62                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.44/0.62                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.62  thf('50', plain,
% 0.44/0.62      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.44/0.62          | ~ (v13_waybel_0 @ X15 @ X16)
% 0.44/0.62          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.44/0.62          | (r2_hidden @ X17 @ X15)
% 0.44/0.62          | ~ (r1_orders_2 @ X16 @ X18 @ X17)
% 0.44/0.62          | ~ (r2_hidden @ X18 @ X15)
% 0.44/0.62          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 0.44/0.62          | ~ (l1_orders_2 @ X16))),
% 0.44/0.62      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.44/0.62  thf('51', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (l1_orders_2 @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.62          | (r2_hidden @ X1 @ sk_B_1)
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.44/0.62  thf('52', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('53', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('54', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.44/0.62          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.62          | (r2_hidden @ X1 @ sk_B_1)
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.44/0.62  thf('55', plain,
% 0.44/0.62      ((![X0 : $i]:
% 0.44/0.62          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62           | (r2_hidden @ X0 @ sk_B_1)
% 0.44/0.62           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.44/0.62           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.44/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['48', '54'])).
% 0.44/0.62  thf('56', plain,
% 0.44/0.62      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.44/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('split', [status(esa)], ['0'])).
% 0.44/0.62  thf('57', plain,
% 0.44/0.62      ((![X0 : $i]:
% 0.44/0.62          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.62           | (r2_hidden @ X0 @ sk_B_1)
% 0.44/0.62           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.44/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('demod', [status(thm)], ['55', '56'])).
% 0.44/0.62  thf('58', plain,
% 0.44/0.62      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62         | (r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 0.44/0.62         | ~ (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62              (u1_struct_0 @ sk_A))))
% 0.44/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['43', '57'])).
% 0.44/0.62  thf('59', plain,
% 0.44/0.62      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62        | (m1_subset_1 @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 0.44/0.62           (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.62  thf('60', plain,
% 0.44/0.62      ((((r2_hidden @ (sk_C @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 0.44/0.62         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.44/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('clc', [status(thm)], ['58', '59'])).
% 0.44/0.62  thf('61', plain,
% 0.44/0.62      (![X1 : $i, X2 : $i]:
% 0.44/0.62         (~ (r2_hidden @ (sk_C @ X1 @ X2) @ X1)
% 0.44/0.62          | ((X2) = (X1))
% 0.44/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.44/0.62  thf('62', plain,
% 0.44/0.62      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 0.44/0.62         | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.44/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.44/0.62  thf('63', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('64', plain,
% 0.44/0.62      (((((u1_struct_0 @ sk_A) = (sk_B_1)) | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 0.44/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('demod', [status(thm)], ['62', '63'])).
% 0.44/0.62  thf('65', plain,
% 0.44/0.62      ((((u1_struct_0 @ sk_A) = (sk_B_1)))
% 0.44/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['64'])).
% 0.44/0.62  thf('66', plain,
% 0.44/0.62      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 0.44/0.62        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('67', plain,
% 0.44/0.62      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('split', [status(esa)], ['66'])).
% 0.44/0.62  thf('68', plain,
% 0.44/0.62      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.44/0.62         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 0.44/0.62             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['65', '67'])).
% 0.44/0.62  thf(rc3_subset_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ?[B:$i]:
% 0.44/0.62       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.44/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.44/0.62  thf('69', plain, (![X3 : $i]: ~ (v1_subset_1 @ (sk_B @ X3) @ X3)),
% 0.44/0.62      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.44/0.62  thf('70', plain,
% 0.44/0.62      (![X3 : $i]: (m1_subset_1 @ (sk_B @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.44/0.62      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.44/0.62  thf(d7_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.62       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.44/0.62  thf('71', plain,
% 0.44/0.62      (![X21 : $i, X22 : $i]:
% 0.44/0.62         (((X22) = (X21))
% 0.44/0.62          | (v1_subset_1 @ X22 @ X21)
% 0.44/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.44/0.62      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.44/0.62  thf('72', plain,
% 0.44/0.62      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['70', '71'])).
% 0.44/0.62  thf('73', plain, (![X3 : $i]: ~ (v1_subset_1 @ (sk_B @ X3) @ X3)),
% 0.44/0.62      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.44/0.62  thf('74', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.44/0.62      inference('clc', [status(thm)], ['72', '73'])).
% 0.44/0.62  thf('75', plain, (![X3 : $i]: ~ (v1_subset_1 @ X3 @ X3)),
% 0.44/0.62      inference('demod', [status(thm)], ['69', '74'])).
% 0.44/0.62  thf('76', plain,
% 0.44/0.62      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.44/0.62       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['68', '75'])).
% 0.44/0.62  thf('77', plain,
% 0.44/0.62      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.44/0.62       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('split', [status(esa)], ['66'])).
% 0.44/0.62  thf('78', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('79', plain,
% 0.44/0.62      (![X21 : $i, X22 : $i]:
% 0.44/0.62         (((X22) = (X21))
% 0.44/0.62          | (v1_subset_1 @ X22 @ X21)
% 0.44/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.44/0.62      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.44/0.62  thf('80', plain,
% 0.44/0.62      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.44/0.62        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['78', '79'])).
% 0.44/0.62  thf('81', plain,
% 0.44/0.62      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('split', [status(esa)], ['0'])).
% 0.44/0.62  thf('82', plain,
% 0.44/0.62      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.44/0.62         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['80', '81'])).
% 0.44/0.62  thf(dt_k3_yellow_0, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_orders_2 @ A ) =>
% 0.44/0.62       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.44/0.62  thf('83', plain,
% 0.44/0.62      (![X10 : $i]:
% 0.44/0.62         ((m1_subset_1 @ (k3_yellow_0 @ X10) @ (u1_struct_0 @ X10))
% 0.44/0.62          | ~ (l1_orders_2 @ X10))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.44/0.62  thf('84', plain,
% 0.44/0.62      ((((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_1) | ~ (l1_orders_2 @ sk_A)))
% 0.44/0.62         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('sup+', [status(thm)], ['82', '83'])).
% 0.44/0.62  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('86', plain,
% 0.44/0.62      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.44/0.62         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('demod', [status(thm)], ['84', '85'])).
% 0.44/0.62  thf(t2_subset, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ A @ B ) =>
% 0.44/0.62       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.44/0.62  thf('87', plain,
% 0.44/0.62      (![X4 : $i, X5 : $i]:
% 0.44/0.62         ((r2_hidden @ X4 @ X5)
% 0.44/0.62          | (v1_xboole_0 @ X5)
% 0.44/0.62          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.44/0.62      inference('cnf', [status(esa)], [t2_subset])).
% 0.44/0.62  thf('88', plain,
% 0.44/0.62      ((((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 0.44/0.62         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['86', '87'])).
% 0.44/0.62  thf('89', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('90', plain,
% 0.44/0.62      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.44/0.62         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.62      inference('clc', [status(thm)], ['88', '89'])).
% 0.44/0.62  thf('91', plain,
% 0.44/0.62      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 0.44/0.62         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('split', [status(esa)], ['66'])).
% 0.44/0.62  thf('92', plain,
% 0.44/0.62      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 0.44/0.62       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['90', '91'])).
% 0.44/0.62  thf('93', plain, ($false),
% 0.44/0.62      inference('sat_resolution*', [status(thm)], ['1', '76', '77', '92'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
