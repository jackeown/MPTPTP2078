%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pPEz3DI2ad

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:13 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 353 expanded)
%              Number of leaves         :   40 ( 117 expanded)
%              Depth                    :   28
%              Number of atoms          : 1669 (6153 expanded)
%              Number of equality atoms :   55 (  66 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

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
    ! [X10: $i] :
      ( ( ( k3_yellow_0 @ X10 )
        = ( k1_yellow_0 @ X10 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('3',plain,(
    ! [X10: $i] :
      ( ( ( k3_yellow_0 @ X10 )
        = ( k1_yellow_0 @ X10 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('4',plain,(
    ! [X10: $i] :
      ( ( ( k3_yellow_0 @ X10 )
        = ( k1_yellow_0 @ X10 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf(t42_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( r1_yellow_0 @ A @ k1_xboole_0 )
        & ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( ( r1_yellow_0 @ X15 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v1_yellow_0 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,(
    ! [X15: $i] :
      ( ( r1_yellow_0 @ X15 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v1_yellow_0 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf(t34_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( ( r1_tarski @ B @ C )
            & ( r1_yellow_0 @ A @ B )
            & ( r1_yellow_0 @ A @ C ) )
         => ( r1_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_orders_2 @ X12 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( k1_yellow_0 @ X12 @ X14 ) )
      | ~ ( r1_yellow_0 @ X12 @ X14 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_yellow_0 @ X12 @ X13 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t34_yellow_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ k1_xboole_0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','19'])).

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
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','29'])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ~ ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','36'])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

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

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( ( k1_yellow_0 @ X21 @ ( k5_waybel_0 @ X21 @ X20 ) )
        = X20 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('44',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
        = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
        = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
      = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k3_yellow_0 @ sk_A ) ) )
        = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['2','51'])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('54',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( ( k1_yellow_0 @ X21 @ ( k5_waybel_0 @ X21 @ X20 ) )
        = X20 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('55',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k3_yellow_0 @ sk_A ) ) )
        = ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k3_yellow_0 @ sk_A ) ) )
        = ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k3_yellow_0 @ sk_A ) ) )
      = ( k3_yellow_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k3_yellow_0 @ sk_A )
      = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['52','62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('66',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X3 @ X4 ) @ X4 )
      | ( X4 = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('67',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( ( k1_yellow_0 @ X21 @ ( k5_waybel_0 @ X21 @ X20 ) )
        = X20 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('69',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X15: $i] :
      ( ( r1_yellow_0 @ X15 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v1_yellow_0 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('79',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('80',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r1_yellow_0 @ X21 @ ( k5_waybel_0 @ X21 @ X20 ) )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('81',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_orders_2 @ X12 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( k1_yellow_0 @ X12 @ X14 ) )
      | ~ ( r1_yellow_0 @ X12 @ X14 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_yellow_0 @ X12 @ X13 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t34_yellow_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['78','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['77','93'])).

thf('95',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference('sup+',[status(thm)],['76','100'])).

thf('102',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['64','102'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('105',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('107',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( X4 = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('109',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['113'])).

thf('115',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['112','114'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('116',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_subset_1 @ X23 @ X22 )
      | ( X23 != X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('117',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( v1_subset_1 @ X22 @ X22 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('118',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('119',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('120',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X22: $i] :
      ~ ( v1_subset_1 @ X22 @ X22 ) ),
    inference(demod,[status(thm)],['117','120'])).

thf('122',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','121'])).

thf('123',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['113'])).

thf('124',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23 = X22 )
      | ( v1_subset_1 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('126',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('128',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('129',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('130',plain,
    ( ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('133',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('134',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['113'])).

thf('138',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','122','123','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pPEz3DI2ad
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.62  % Solved by: fo/fo7.sh
% 0.37/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.62  % done 301 iterations in 0.159s
% 0.37/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.62  % SZS output start Refutation
% 0.37/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.62  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.37/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.62  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.37/0.62  thf(k5_waybel_0_type, type, k5_waybel_0: $i > $i > $i).
% 0.37/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.62  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.37/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.62  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.37/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.62  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.37/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.62  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.37/0.62  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.37/0.62  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.37/0.62  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.37/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.62  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.37/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.62  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.37/0.62  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.37/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.62  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.37/0.62  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.37/0.62  thf(t8_waybel_7, conjecture,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.62         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.37/0.62         ( l1_orders_2 @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.37/0.62             ( v13_waybel_0 @ B @ A ) & 
% 0.37/0.62             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.62           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.37/0.62             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.37/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.62    (~( ![A:$i]:
% 0.37/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.62            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.37/0.62            ( l1_orders_2 @ A ) ) =>
% 0.37/0.62          ( ![B:$i]:
% 0.37/0.62            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.37/0.62                ( v13_waybel_0 @ B @ A ) & 
% 0.37/0.62                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.62              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.37/0.62                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.37/0.62    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.37/0.62  thf('0', plain,
% 0.37/0.62      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.37/0.62        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('1', plain,
% 0.37/0.62      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.37/0.62       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('split', [status(esa)], ['0'])).
% 0.37/0.62  thf(d11_yellow_0, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_orders_2 @ A ) =>
% 0.37/0.62       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.37/0.62  thf('2', plain,
% 0.37/0.62      (![X10 : $i]:
% 0.37/0.62         (((k3_yellow_0 @ X10) = (k1_yellow_0 @ X10 @ k1_xboole_0))
% 0.37/0.62          | ~ (l1_orders_2 @ X10))),
% 0.37/0.62      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.37/0.62  thf('3', plain,
% 0.37/0.62      (![X10 : $i]:
% 0.37/0.62         (((k3_yellow_0 @ X10) = (k1_yellow_0 @ X10 @ k1_xboole_0))
% 0.37/0.62          | ~ (l1_orders_2 @ X10))),
% 0.37/0.62      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.37/0.62  thf('4', plain,
% 0.37/0.62      (![X10 : $i]:
% 0.37/0.62         (((k3_yellow_0 @ X10) = (k1_yellow_0 @ X10 @ k1_xboole_0))
% 0.37/0.62          | ~ (l1_orders_2 @ X10))),
% 0.37/0.62      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.37/0.62  thf(t42_yellow_0, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.37/0.62         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.62       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 0.37/0.62         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.62  thf('5', plain,
% 0.37/0.62      (![X15 : $i]:
% 0.37/0.62         ((r1_yellow_0 @ X15 @ k1_xboole_0)
% 0.37/0.62          | ~ (l1_orders_2 @ X15)
% 0.37/0.62          | ~ (v1_yellow_0 @ X15)
% 0.37/0.62          | ~ (v5_orders_2 @ X15)
% 0.37/0.62          | (v2_struct_0 @ X15))),
% 0.37/0.62      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.37/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.62  thf('6', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.62  thf('7', plain,
% 0.37/0.62      (![X15 : $i]:
% 0.37/0.62         ((r1_yellow_0 @ X15 @ k1_xboole_0)
% 0.37/0.62          | ~ (l1_orders_2 @ X15)
% 0.37/0.62          | ~ (v1_yellow_0 @ X15)
% 0.37/0.62          | ~ (v5_orders_2 @ X15)
% 0.37/0.62          | (v2_struct_0 @ X15))),
% 0.37/0.62      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.37/0.62  thf(t34_yellow_0, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_orders_2 @ A ) =>
% 0.37/0.62       ( ![B:$i,C:$i]:
% 0.37/0.62         ( ( ( r1_tarski @ B @ C ) & ( r1_yellow_0 @ A @ B ) & 
% 0.37/0.62             ( r1_yellow_0 @ A @ C ) ) =>
% 0.37/0.62           ( r1_orders_2 @
% 0.37/0.62             A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) ))).
% 0.37/0.62  thf('8', plain,
% 0.37/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.62         ((r1_orders_2 @ X12 @ (k1_yellow_0 @ X12 @ X13) @ 
% 0.37/0.62           (k1_yellow_0 @ X12 @ X14))
% 0.37/0.62          | ~ (r1_yellow_0 @ X12 @ X14)
% 0.37/0.62          | ~ (r1_tarski @ X13 @ X14)
% 0.37/0.62          | ~ (r1_yellow_0 @ X12 @ X13)
% 0.37/0.62          | ~ (l1_orders_2 @ X12))),
% 0.37/0.62      inference('cnf', [status(esa)], [t34_yellow_0])).
% 0.37/0.62  thf('9', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((v2_struct_0 @ X0)
% 0.37/0.62          | ~ (v5_orders_2 @ X0)
% 0.37/0.62          | ~ (v1_yellow_0 @ X0)
% 0.37/0.62          | ~ (l1_orders_2 @ X0)
% 0.37/0.62          | ~ (l1_orders_2 @ X0)
% 0.37/0.62          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.37/0.62          | ~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.37/0.62          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 0.37/0.62             (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.62  thf('10', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 0.37/0.62           (k1_yellow_0 @ X0 @ k1_xboole_0))
% 0.37/0.62          | ~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.37/0.62          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.37/0.62          | ~ (l1_orders_2 @ X0)
% 0.37/0.62          | ~ (v1_yellow_0 @ X0)
% 0.37/0.62          | ~ (v5_orders_2 @ X0)
% 0.37/0.62          | (v2_struct_0 @ X0))),
% 0.37/0.62      inference('simplify', [status(thm)], ['9'])).
% 0.37/0.62  thf('11', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ X0)
% 0.37/0.62          | ~ (v5_orders_2 @ X0)
% 0.37/0.62          | ~ (v1_yellow_0 @ X0)
% 0.37/0.62          | ~ (l1_orders_2 @ X0)
% 0.37/0.62          | ~ (r1_yellow_0 @ X0 @ k1_xboole_0)
% 0.37/0.62          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.37/0.62             (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['6', '10'])).
% 0.37/0.62  thf('12', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((v2_struct_0 @ X0)
% 0.37/0.62          | ~ (v5_orders_2 @ X0)
% 0.37/0.62          | ~ (v1_yellow_0 @ X0)
% 0.37/0.62          | ~ (l1_orders_2 @ X0)
% 0.37/0.62          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.37/0.62             (k1_yellow_0 @ X0 @ k1_xboole_0))
% 0.37/0.62          | ~ (l1_orders_2 @ X0)
% 0.37/0.62          | ~ (v1_yellow_0 @ X0)
% 0.37/0.62          | ~ (v5_orders_2 @ X0)
% 0.37/0.62          | (v2_struct_0 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['5', '11'])).
% 0.37/0.62  thf('13', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.37/0.62           (k1_yellow_0 @ X0 @ k1_xboole_0))
% 0.37/0.62          | ~ (l1_orders_2 @ X0)
% 0.37/0.62          | ~ (v1_yellow_0 @ X0)
% 0.37/0.62          | ~ (v5_orders_2 @ X0)
% 0.37/0.62          | (v2_struct_0 @ X0))),
% 0.37/0.62      inference('simplify', [status(thm)], ['12'])).
% 0.37/0.62  thf('14', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 0.37/0.62           (k1_yellow_0 @ X0 @ k1_xboole_0))
% 0.37/0.62          | ~ (l1_orders_2 @ X0)
% 0.37/0.62          | (v2_struct_0 @ X0)
% 0.37/0.62          | ~ (v5_orders_2 @ X0)
% 0.37/0.62          | ~ (v1_yellow_0 @ X0)
% 0.37/0.62          | ~ (l1_orders_2 @ X0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['4', '13'])).
% 0.37/0.62  thf('15', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_yellow_0 @ X0)
% 0.37/0.62          | ~ (v5_orders_2 @ X0)
% 0.37/0.62          | (v2_struct_0 @ X0)
% 0.37/0.62          | ~ (l1_orders_2 @ X0)
% 0.37/0.62          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 0.37/0.62             (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.62  thf('16', plain,
% 0.37/0.62      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('split', [status(esa)], ['0'])).
% 0.37/0.62  thf('17', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(t4_subset, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.37/0.62       ( m1_subset_1 @ A @ C ) ))).
% 0.37/0.62  thf('18', plain,
% 0.37/0.62      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.62         (~ (r2_hidden @ X7 @ X8)
% 0.37/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.37/0.62          | (m1_subset_1 @ X7 @ X9))),
% 0.37/0.62      inference('cnf', [status(esa)], [t4_subset])).
% 0.37/0.62  thf('19', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.62  thf('20', plain,
% 0.37/0.62      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['16', '19'])).
% 0.37/0.62  thf('21', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(d20_waybel_0, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_orders_2 @ A ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.62           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.37/0.62             ( ![C:$i]:
% 0.37/0.62               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.62                 ( ![D:$i]:
% 0.37/0.62                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.62                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.37/0.62                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.62  thf('22', plain,
% 0.37/0.62      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.62          | ~ (v13_waybel_0 @ X16 @ X17)
% 0.37/0.62          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.37/0.62          | (r2_hidden @ X18 @ X16)
% 0.37/0.62          | ~ (r1_orders_2 @ X17 @ X19 @ X18)
% 0.37/0.62          | ~ (r2_hidden @ X19 @ X16)
% 0.37/0.62          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.37/0.62          | ~ (l1_orders_2 @ X17))),
% 0.37/0.62      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.37/0.62  thf('23', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (~ (l1_orders_2 @ sk_A)
% 0.37/0.62          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | ~ (r2_hidden @ X0 @ sk_B)
% 0.37/0.62          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.37/0.62          | (r2_hidden @ X1 @ sk_B)
% 0.37/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.62  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('25', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('26', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62          | ~ (r2_hidden @ X0 @ sk_B)
% 0.37/0.62          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.37/0.62          | (r2_hidden @ X1 @ sk_B)
% 0.37/0.62          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.37/0.62  thf('27', plain,
% 0.37/0.62      ((![X0 : $i]:
% 0.37/0.62          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62           | (r2_hidden @ X0 @ sk_B)
% 0.37/0.62           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.37/0.62           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['20', '26'])).
% 0.37/0.62  thf('28', plain,
% 0.37/0.62      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('split', [status(esa)], ['0'])).
% 0.37/0.62  thf('29', plain,
% 0.37/0.62      ((![X0 : $i]:
% 0.37/0.62          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62           | (r2_hidden @ X0 @ sk_B)
% 0.37/0.62           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.37/0.62  thf('30', plain,
% 0.37/0.62      (((~ (l1_orders_2 @ sk_A)
% 0.37/0.62         | (v2_struct_0 @ sk_A)
% 0.37/0.62         | ~ (v5_orders_2 @ sk_A)
% 0.37/0.62         | ~ (v1_yellow_0 @ sk_A)
% 0.37/0.62         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ sk_B)
% 0.37/0.62         | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.37/0.62              (u1_struct_0 @ sk_A))))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['15', '29'])).
% 0.37/0.62  thf('31', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('32', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('33', plain, ((v1_yellow_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('34', plain,
% 0.37/0.62      ((((v2_struct_0 @ sk_A)
% 0.37/0.62         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ sk_B)
% 0.37/0.62         | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.37/0.62              (u1_struct_0 @ sk_A))))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.37/0.62  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('36', plain,
% 0.37/0.62      (((~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.37/0.62            (u1_struct_0 @ sk_A))
% 0.37/0.62         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ sk_B)))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('clc', [status(thm)], ['34', '35'])).
% 0.37/0.62  thf('37', plain,
% 0.37/0.62      (((~ (m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.37/0.62         | ~ (l1_orders_2 @ sk_A)
% 0.37/0.62         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ sk_B)))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['3', '36'])).
% 0.37/0.62  thf('38', plain,
% 0.37/0.62      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['16', '19'])).
% 0.37/0.62  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('40', plain,
% 0.37/0.62      (((r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ sk_B))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.37/0.62  thf('41', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.37/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.62  thf('42', plain,
% 0.37/0.62      (((m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.37/0.62         (u1_struct_0 @ sk_A)))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.62  thf(t34_waybel_0, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.62         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.62           ( ( r1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) ) & 
% 0.37/0.62             ( ( k1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.37/0.62  thf('43', plain,
% 0.37/0.62      (![X20 : $i, X21 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.37/0.62          | ((k1_yellow_0 @ X21 @ (k5_waybel_0 @ X21 @ X20)) = (X20))
% 0.37/0.62          | ~ (l1_orders_2 @ X21)
% 0.37/0.62          | ~ (v5_orders_2 @ X21)
% 0.37/0.62          | ~ (v4_orders_2 @ X21)
% 0.37/0.62          | ~ (v3_orders_2 @ X21)
% 0.37/0.62          | (v2_struct_0 @ X21))),
% 0.37/0.62      inference('cnf', [status(esa)], [t34_waybel_0])).
% 0.37/0.62  thf('44', plain,
% 0.37/0.62      ((((v2_struct_0 @ sk_A)
% 0.37/0.62         | ~ (v3_orders_2 @ sk_A)
% 0.37/0.62         | ~ (v4_orders_2 @ sk_A)
% 0.37/0.62         | ~ (v5_orders_2 @ sk_A)
% 0.37/0.62         | ~ (l1_orders_2 @ sk_A)
% 0.37/0.62         | ((k1_yellow_0 @ sk_A @ 
% 0.37/0.62             (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 0.37/0.62             = (k1_yellow_0 @ sk_A @ k1_xboole_0))))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.62  thf('45', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('46', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('47', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('48', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('49', plain,
% 0.37/0.62      ((((v2_struct_0 @ sk_A)
% 0.37/0.62         | ((k1_yellow_0 @ sk_A @ 
% 0.37/0.62             (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 0.37/0.62             = (k1_yellow_0 @ sk_A @ k1_xboole_0))))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 0.37/0.62  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('51', plain,
% 0.37/0.62      ((((k1_yellow_0 @ sk_A @ 
% 0.37/0.62          (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 0.37/0.62          = (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('clc', [status(thm)], ['49', '50'])).
% 0.37/0.62  thf('52', plain,
% 0.37/0.62      (((((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ (k3_yellow_0 @ sk_A)))
% 0.37/0.62           = (k1_yellow_0 @ sk_A @ k1_xboole_0))
% 0.37/0.62         | ~ (l1_orders_2 @ sk_A)))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['2', '51'])).
% 0.37/0.62  thf('53', plain,
% 0.37/0.62      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['16', '19'])).
% 0.37/0.62  thf('54', plain,
% 0.37/0.62      (![X20 : $i, X21 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.37/0.62          | ((k1_yellow_0 @ X21 @ (k5_waybel_0 @ X21 @ X20)) = (X20))
% 0.37/0.62          | ~ (l1_orders_2 @ X21)
% 0.37/0.62          | ~ (v5_orders_2 @ X21)
% 0.37/0.62          | ~ (v4_orders_2 @ X21)
% 0.37/0.62          | ~ (v3_orders_2 @ X21)
% 0.37/0.62          | (v2_struct_0 @ X21))),
% 0.37/0.62      inference('cnf', [status(esa)], [t34_waybel_0])).
% 0.37/0.62  thf('55', plain,
% 0.37/0.62      ((((v2_struct_0 @ sk_A)
% 0.37/0.62         | ~ (v3_orders_2 @ sk_A)
% 0.37/0.62         | ~ (v4_orders_2 @ sk_A)
% 0.37/0.62         | ~ (v5_orders_2 @ sk_A)
% 0.37/0.62         | ~ (l1_orders_2 @ sk_A)
% 0.37/0.62         | ((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ (k3_yellow_0 @ sk_A)))
% 0.37/0.62             = (k3_yellow_0 @ sk_A))))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.62  thf('56', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('57', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('58', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('59', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('60', plain,
% 0.37/0.62      ((((v2_struct_0 @ sk_A)
% 0.37/0.62         | ((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ (k3_yellow_0 @ sk_A)))
% 0.37/0.62             = (k3_yellow_0 @ sk_A))))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.37/0.62  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('62', plain,
% 0.37/0.62      ((((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ (k3_yellow_0 @ sk_A)))
% 0.37/0.62          = (k3_yellow_0 @ sk_A)))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('clc', [status(thm)], ['60', '61'])).
% 0.37/0.62  thf('63', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('64', plain,
% 0.37/0.62      ((((k3_yellow_0 @ sk_A) = (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['52', '62', '63'])).
% 0.37/0.62  thf('65', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(t49_subset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.62       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.37/0.62         ( ( A ) = ( B ) ) ) ))).
% 0.37/0.62  thf('66', plain,
% 0.37/0.62      (![X3 : $i, X4 : $i]:
% 0.37/0.62         ((m1_subset_1 @ (sk_C @ X3 @ X4) @ X4)
% 0.37/0.62          | ((X4) = (X3))
% 0.37/0.62          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.37/0.62  thf('67', plain,
% 0.37/0.62      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62        | (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.37/0.62           (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['65', '66'])).
% 0.37/0.62  thf('68', plain,
% 0.37/0.62      (![X20 : $i, X21 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.37/0.62          | ((k1_yellow_0 @ X21 @ (k5_waybel_0 @ X21 @ X20)) = (X20))
% 0.37/0.62          | ~ (l1_orders_2 @ X21)
% 0.37/0.62          | ~ (v5_orders_2 @ X21)
% 0.37/0.62          | ~ (v4_orders_2 @ X21)
% 0.37/0.62          | ~ (v3_orders_2 @ X21)
% 0.37/0.62          | (v2_struct_0 @ X21))),
% 0.37/0.62      inference('cnf', [status(esa)], [t34_waybel_0])).
% 0.37/0.62  thf('69', plain,
% 0.37/0.62      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62        | (v2_struct_0 @ sk_A)
% 0.37/0.62        | ~ (v3_orders_2 @ sk_A)
% 0.37/0.62        | ~ (v4_orders_2 @ sk_A)
% 0.37/0.62        | ~ (v5_orders_2 @ sk_A)
% 0.37/0.62        | ~ (l1_orders_2 @ sk_A)
% 0.37/0.62        | ((k1_yellow_0 @ sk_A @ 
% 0.37/0.62            (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.37/0.62            = (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['67', '68'])).
% 0.37/0.62  thf('70', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('71', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('72', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('73', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('74', plain,
% 0.37/0.62      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62        | (v2_struct_0 @ sk_A)
% 0.37/0.62        | ((k1_yellow_0 @ sk_A @ 
% 0.37/0.62            (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.37/0.62            = (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.62      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.37/0.62  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('76', plain,
% 0.37/0.62      ((((k1_yellow_0 @ sk_A @ 
% 0.37/0.62          (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.37/0.62          = (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.37/0.62        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.37/0.62      inference('clc', [status(thm)], ['74', '75'])).
% 0.37/0.62  thf('77', plain,
% 0.37/0.62      (![X15 : $i]:
% 0.37/0.62         ((r1_yellow_0 @ X15 @ k1_xboole_0)
% 0.37/0.62          | ~ (l1_orders_2 @ X15)
% 0.37/0.62          | ~ (v1_yellow_0 @ X15)
% 0.37/0.62          | ~ (v5_orders_2 @ X15)
% 0.37/0.62          | (v2_struct_0 @ X15))),
% 0.37/0.62      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.37/0.62  thf('78', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.62  thf('79', plain,
% 0.37/0.62      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62        | (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.37/0.62           (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['65', '66'])).
% 0.37/0.62  thf('80', plain,
% 0.37/0.62      (![X20 : $i, X21 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.37/0.62          | (r1_yellow_0 @ X21 @ (k5_waybel_0 @ X21 @ X20))
% 0.37/0.62          | ~ (l1_orders_2 @ X21)
% 0.37/0.62          | ~ (v5_orders_2 @ X21)
% 0.37/0.62          | ~ (v4_orders_2 @ X21)
% 0.37/0.62          | ~ (v3_orders_2 @ X21)
% 0.37/0.62          | (v2_struct_0 @ X21))),
% 0.37/0.62      inference('cnf', [status(esa)], [t34_waybel_0])).
% 0.37/0.62  thf('81', plain,
% 0.37/0.62      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62        | (v2_struct_0 @ sk_A)
% 0.37/0.62        | ~ (v3_orders_2 @ sk_A)
% 0.37/0.62        | ~ (v4_orders_2 @ sk_A)
% 0.37/0.62        | ~ (v5_orders_2 @ sk_A)
% 0.37/0.62        | ~ (l1_orders_2 @ sk_A)
% 0.37/0.62        | (r1_yellow_0 @ sk_A @ 
% 0.37/0.62           (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['79', '80'])).
% 0.37/0.62  thf('82', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('83', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('84', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('86', plain,
% 0.37/0.62      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62        | (v2_struct_0 @ sk_A)
% 0.37/0.62        | (r1_yellow_0 @ sk_A @ 
% 0.37/0.62           (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.62      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 0.37/0.62  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('88', plain,
% 0.37/0.62      (((r1_yellow_0 @ sk_A @ 
% 0.37/0.62         (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.37/0.62        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.37/0.62      inference('clc', [status(thm)], ['86', '87'])).
% 0.37/0.62  thf('89', plain,
% 0.37/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.62         ((r1_orders_2 @ X12 @ (k1_yellow_0 @ X12 @ X13) @ 
% 0.37/0.62           (k1_yellow_0 @ X12 @ X14))
% 0.37/0.62          | ~ (r1_yellow_0 @ X12 @ X14)
% 0.37/0.62          | ~ (r1_tarski @ X13 @ X14)
% 0.37/0.62          | ~ (r1_yellow_0 @ X12 @ X13)
% 0.37/0.62          | ~ (l1_orders_2 @ X12))),
% 0.37/0.62      inference('cnf', [status(esa)], [t34_yellow_0])).
% 0.37/0.62  thf('90', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.62          | ~ (r1_yellow_0 @ sk_A @ X0)
% 0.37/0.62          | ~ (r1_tarski @ X0 @ 
% 0.37/0.62               (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.37/0.62          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.37/0.62             (k1_yellow_0 @ sk_A @ 
% 0.37/0.62              (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['88', '89'])).
% 0.37/0.62  thf('91', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('92', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62          | ~ (r1_yellow_0 @ sk_A @ X0)
% 0.37/0.62          | ~ (r1_tarski @ X0 @ 
% 0.37/0.62               (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.37/0.62          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.37/0.62             (k1_yellow_0 @ sk_A @ 
% 0.37/0.62              (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.62      inference('demod', [status(thm)], ['90', '91'])).
% 0.37/0.62  thf('93', plain,
% 0.37/0.62      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.37/0.62         (k1_yellow_0 @ sk_A @ 
% 0.37/0.62          (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))))
% 0.37/0.62        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 0.37/0.62        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['78', '92'])).
% 0.37/0.62  thf('94', plain,
% 0.37/0.62      (((v2_struct_0 @ sk_A)
% 0.37/0.62        | ~ (v5_orders_2 @ sk_A)
% 0.37/0.62        | ~ (v1_yellow_0 @ sk_A)
% 0.37/0.62        | ~ (l1_orders_2 @ sk_A)
% 0.37/0.62        | ((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.37/0.62           (k1_yellow_0 @ sk_A @ 
% 0.37/0.62            (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['77', '93'])).
% 0.37/0.62  thf('95', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('96', plain, ((v1_yellow_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('97', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('98', plain,
% 0.37/0.62      (((v2_struct_0 @ sk_A)
% 0.37/0.62        | ((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.37/0.62           (k1_yellow_0 @ sk_A @ 
% 0.37/0.62            (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))))),
% 0.37/0.62      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 0.37/0.62  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('100', plain,
% 0.37/0.62      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.37/0.62         (k1_yellow_0 @ sk_A @ 
% 0.37/0.62          (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))))
% 0.37/0.62        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.37/0.62      inference('clc', [status(thm)], ['98', '99'])).
% 0.37/0.62  thf('101', plain,
% 0.37/0.62      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.37/0.62         (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.37/0.62        | ((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['76', '100'])).
% 0.37/0.62  thf('102', plain,
% 0.37/0.62      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.37/0.62           (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.62      inference('simplify', [status(thm)], ['101'])).
% 0.37/0.62  thf('103', plain,
% 0.37/0.62      ((((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.37/0.62          (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.37/0.62         | ((u1_struct_0 @ sk_A) = (sk_B))))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['64', '102'])).
% 0.37/0.62  thf('104', plain,
% 0.37/0.62      ((![X0 : $i]:
% 0.37/0.62          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.62           | (r2_hidden @ X0 @ sk_B)
% 0.37/0.62           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.37/0.62  thf('105', plain,
% 0.37/0.62      (((((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62         | (r2_hidden @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.37/0.62         | ~ (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.37/0.62              (u1_struct_0 @ sk_A))))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['103', '104'])).
% 0.37/0.62  thf('106', plain,
% 0.37/0.62      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62        | (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.37/0.62           (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['65', '66'])).
% 0.37/0.62  thf('107', plain,
% 0.37/0.62      ((((r2_hidden @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.37/0.62         | ((u1_struct_0 @ sk_A) = (sk_B))))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('clc', [status(thm)], ['105', '106'])).
% 0.37/0.62  thf('108', plain,
% 0.37/0.62      (![X3 : $i, X4 : $i]:
% 0.37/0.62         (~ (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 0.37/0.62          | ((X4) = (X3))
% 0.37/0.62          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.37/0.62  thf('109', plain,
% 0.37/0.62      (((((u1_struct_0 @ sk_A) = (sk_B))
% 0.37/0.62         | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.62         | ((u1_struct_0 @ sk_A) = (sk_B))))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['107', '108'])).
% 0.37/0.62  thf('110', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('111', plain,
% 0.37/0.62      (((((u1_struct_0 @ sk_A) = (sk_B)) | ((u1_struct_0 @ sk_A) = (sk_B))))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['109', '110'])).
% 0.37/0.62  thf('112', plain,
% 0.37/0.62      ((((u1_struct_0 @ sk_A) = (sk_B)))
% 0.37/0.62         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['111'])).
% 0.37/0.62  thf('113', plain,
% 0.37/0.62      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.37/0.62        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('114', plain,
% 0.37/0.62      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.37/0.62         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.62      inference('split', [status(esa)], ['113'])).
% 0.37/0.62  thf('115', plain,
% 0.37/0.62      (((v1_subset_1 @ sk_B @ sk_B))
% 0.37/0.62         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.37/0.62             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['112', '114'])).
% 0.37/0.62  thf(d7_subset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.62       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.37/0.62  thf('116', plain,
% 0.37/0.62      (![X22 : $i, X23 : $i]:
% 0.37/0.62         (~ (v1_subset_1 @ X23 @ X22)
% 0.37/0.62          | ((X23) != (X22))
% 0.37/0.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.37/0.62      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.37/0.62  thf('117', plain,
% 0.37/0.62      (![X22 : $i]:
% 0.37/0.62         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X22))
% 0.37/0.62          | ~ (v1_subset_1 @ X22 @ X22))),
% 0.37/0.62      inference('simplify', [status(thm)], ['116'])).
% 0.37/0.62  thf(dt_k2_subset_1, axiom,
% 0.37/0.62    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.62  thf('118', plain,
% 0.37/0.62      (![X2 : $i]: (m1_subset_1 @ (k2_subset_1 @ X2) @ (k1_zfmisc_1 @ X2))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.37/0.62  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.37/0.62  thf('119', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.37/0.62  thf('120', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.37/0.62      inference('demod', [status(thm)], ['118', '119'])).
% 0.37/0.62  thf('121', plain, (![X22 : $i]: ~ (v1_subset_1 @ X22 @ X22)),
% 0.37/0.62      inference('demod', [status(thm)], ['117', '120'])).
% 0.37/0.62  thf('122', plain,
% 0.37/0.62      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.37/0.62       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['115', '121'])).
% 0.37/0.62  thf('123', plain,
% 0.37/0.62      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.37/0.62       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('split', [status(esa)], ['113'])).
% 0.37/0.62  thf('124', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('125', plain,
% 0.37/0.62      (![X22 : $i, X23 : $i]:
% 0.37/0.62         (((X23) = (X22))
% 0.37/0.62          | (v1_subset_1 @ X23 @ X22)
% 0.37/0.62          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.37/0.62      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.37/0.62  thf('126', plain,
% 0.37/0.62      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.37/0.62        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['124', '125'])).
% 0.37/0.62  thf('127', plain,
% 0.37/0.62      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.37/0.62         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.62      inference('split', [status(esa)], ['0'])).
% 0.37/0.62  thf('128', plain,
% 0.37/0.62      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.37/0.62         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['126', '127'])).
% 0.37/0.62  thf(dt_k3_yellow_0, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_orders_2 @ A ) =>
% 0.37/0.62       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.37/0.62  thf('129', plain,
% 0.37/0.62      (![X11 : $i]:
% 0.37/0.62         ((m1_subset_1 @ (k3_yellow_0 @ X11) @ (u1_struct_0 @ X11))
% 0.37/0.62          | ~ (l1_orders_2 @ X11))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.37/0.62  thf('130', plain,
% 0.37/0.62      ((((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B) | ~ (l1_orders_2 @ sk_A)))
% 0.37/0.62         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.62      inference('sup+', [status(thm)], ['128', '129'])).
% 0.37/0.62  thf('131', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('132', plain,
% 0.37/0.62      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.37/0.62         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.62      inference('demod', [status(thm)], ['130', '131'])).
% 0.37/0.62  thf(t2_subset, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.62       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.62  thf('133', plain,
% 0.37/0.62      (![X5 : $i, X6 : $i]:
% 0.37/0.62         ((r2_hidden @ X5 @ X6)
% 0.37/0.62          | (v1_xboole_0 @ X6)
% 0.37/0.62          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.37/0.62      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.62  thf('134', plain,
% 0.37/0.62      ((((v1_xboole_0 @ sk_B) | (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.37/0.62         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['132', '133'])).
% 0.37/0.62  thf('135', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('136', plain,
% 0.37/0.62      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.37/0.62         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.37/0.62      inference('clc', [status(thm)], ['134', '135'])).
% 0.37/0.62  thf('137', plain,
% 0.37/0.62      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.37/0.62         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.37/0.62      inference('split', [status(esa)], ['113'])).
% 0.37/0.62  thf('138', plain,
% 0.37/0.62      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.37/0.62       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['136', '137'])).
% 0.37/0.62  thf('139', plain, ($false),
% 0.37/0.62      inference('sat_resolution*', [status(thm)], ['1', '122', '123', '138'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
