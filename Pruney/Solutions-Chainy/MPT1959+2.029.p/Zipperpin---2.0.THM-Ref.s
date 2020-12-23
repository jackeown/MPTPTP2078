%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZO3lZg4ezq

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:13 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 210 expanded)
%              Number of leaves         :   40 (  77 expanded)
%              Depth                    :   24
%              Number of atoms          : 1122 (3439 expanded)
%              Number of equality atoms :   43 (  49 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X2 @ X3 ) @ X3 )
      | ( X3 = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('5',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('7',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
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
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
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

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('17',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r1_yellow_0 @ X21 @ ( k5_waybel_0 @ X21 @ X20 ) )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('19',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
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
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_orders_2 @ X12 @ ( k1_yellow_0 @ X12 @ X13 ) @ ( k1_yellow_0 @ X12 @ X14 ) )
      | ~ ( r1_yellow_0 @ X12 @ X14 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_yellow_0 @ X12 @ X13 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t34_yellow_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ~ ( r1_tarski @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
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
      = sk_B )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference('sup+',[status(thm)],['14','38'])).

thf('40',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference('sup+',[status(thm)],['2','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('46',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
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

thf('50',plain,(
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

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','57'])).

thf('59',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('60',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X2 @ X3 ) @ X2 )
      | ( X3 = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('62',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['65','67'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('69',plain,(
    ! [X4: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X4 ) @ X4 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('70',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('71',plain,(
    ! [X4: $i] :
      ~ ( v1_subset_1 @ X4 @ X4 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['66'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('75',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23 = X22 )
      | ( v1_subset_1 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('76',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('79',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('80',plain,
    ( ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('83',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('84',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['66'])).

thf('88',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','72','73','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZO3lZg4ezq
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 160 iterations in 0.085s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.36/0.55  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.55  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.36/0.55  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.36/0.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.36/0.55  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.36/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.55  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.36/0.55  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.36/0.55  thf(k5_waybel_0_type, type, k5_waybel_0: $i > $i > $i).
% 0.36/0.55  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(t8_waybel_7, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.36/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.36/0.55         ( l1_orders_2 @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.36/0.55             ( v13_waybel_0 @ B @ A ) & 
% 0.36/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.55           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.36/0.55             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.36/0.55            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.36/0.55            ( l1_orders_2 @ A ) ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.36/0.55                ( v13_waybel_0 @ B @ A ) & 
% 0.36/0.55                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.55              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.36/0.55                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.36/0.55        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.36/0.55       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('split', [status(esa)], ['0'])).
% 0.36/0.55  thf(d11_yellow_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_orders_2 @ A ) =>
% 0.36/0.55       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (![X10 : $i]:
% 0.36/0.55         (((k3_yellow_0 @ X10) = (k1_yellow_0 @ X10 @ k1_xboole_0))
% 0.36/0.55          | ~ (l1_orders_2 @ X10))),
% 0.36/0.55      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t49_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.36/0.55         ( ( A ) = ( B ) ) ) ))).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (sk_C @ X2 @ X3) @ X3)
% 0.36/0.55          | ((X3) = (X2))
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55        | (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.36/0.55           (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.55  thf(t34_waybel_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.36/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55           ( ( r1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) ) & 
% 0.36/0.55             ( ( k1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X20 : $i, X21 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.36/0.55          | ((k1_yellow_0 @ X21 @ (k5_waybel_0 @ X21 @ X20)) = (X20))
% 0.36/0.55          | ~ (l1_orders_2 @ X21)
% 0.36/0.55          | ~ (v5_orders_2 @ X21)
% 0.36/0.55          | ~ (v4_orders_2 @ X21)
% 0.36/0.55          | ~ (v3_orders_2 @ X21)
% 0.36/0.55          | (v2_struct_0 @ X21))),
% 0.36/0.55      inference('cnf', [status(esa)], [t34_waybel_0])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v3_orders_2 @ sk_A)
% 0.36/0.55        | ~ (v4_orders_2 @ sk_A)
% 0.36/0.55        | ~ (v5_orders_2 @ sk_A)
% 0.36/0.55        | ~ (l1_orders_2 @ sk_A)
% 0.36/0.55        | ((k1_yellow_0 @ sk_A @ 
% 0.36/0.55            (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.36/0.55            = (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.55  thf('8', plain, ((v3_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('9', plain, ((v4_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('10', plain, ((v5_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | ((k1_yellow_0 @ sk_A @ 
% 0.36/0.55            (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.36/0.55            = (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.36/0.55  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      ((((k1_yellow_0 @ sk_A @ 
% 0.36/0.55          (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.36/0.55          = (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.36/0.55      inference('clc', [status(thm)], ['12', '13'])).
% 0.36/0.55  thf(t42_yellow_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.36/0.55         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.36/0.55       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 0.36/0.55         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X15 : $i]:
% 0.36/0.55         ((r1_yellow_0 @ X15 @ k1_xboole_0)
% 0.36/0.55          | ~ (l1_orders_2 @ X15)
% 0.36/0.55          | ~ (v1_yellow_0 @ X15)
% 0.36/0.55          | ~ (v5_orders_2 @ X15)
% 0.36/0.55          | (v2_struct_0 @ X15))),
% 0.36/0.55      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.36/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.55  thf('16', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55        | (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.36/0.55           (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X20 : $i, X21 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.36/0.55          | (r1_yellow_0 @ X21 @ (k5_waybel_0 @ X21 @ X20))
% 0.36/0.55          | ~ (l1_orders_2 @ X21)
% 0.36/0.55          | ~ (v5_orders_2 @ X21)
% 0.36/0.55          | ~ (v4_orders_2 @ X21)
% 0.36/0.55          | ~ (v3_orders_2 @ X21)
% 0.36/0.55          | (v2_struct_0 @ X21))),
% 0.36/0.55      inference('cnf', [status(esa)], [t34_waybel_0])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v3_orders_2 @ sk_A)
% 0.36/0.55        | ~ (v4_orders_2 @ sk_A)
% 0.36/0.55        | ~ (v5_orders_2 @ sk_A)
% 0.36/0.55        | ~ (l1_orders_2 @ sk_A)
% 0.36/0.55        | (r1_yellow_0 @ sk_A @ 
% 0.36/0.55           (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.55  thf('20', plain, ((v3_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('21', plain, ((v4_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('22', plain, ((v5_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55        | (v2_struct_0 @ sk_A)
% 0.36/0.55        | (r1_yellow_0 @ sk_A @ 
% 0.36/0.55           (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.55      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.36/0.55  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (((r1_yellow_0 @ sk_A @ 
% 0.36/0.55         (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.36/0.55      inference('clc', [status(thm)], ['24', '25'])).
% 0.36/0.55  thf(t34_yellow_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_orders_2 @ A ) =>
% 0.36/0.55       ( ![B:$i,C:$i]:
% 0.36/0.55         ( ( ( r1_tarski @ B @ C ) & ( r1_yellow_0 @ A @ B ) & 
% 0.36/0.55             ( r1_yellow_0 @ A @ C ) ) =>
% 0.36/0.55           ( r1_orders_2 @
% 0.36/0.55             A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) ))).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.55         ((r1_orders_2 @ X12 @ (k1_yellow_0 @ X12 @ X13) @ 
% 0.36/0.55           (k1_yellow_0 @ X12 @ X14))
% 0.36/0.55          | ~ (r1_yellow_0 @ X12 @ X14)
% 0.36/0.55          | ~ (r1_tarski @ X13 @ X14)
% 0.36/0.55          | ~ (r1_yellow_0 @ X12 @ X13)
% 0.36/0.55          | ~ (l1_orders_2 @ X12))),
% 0.36/0.55      inference('cnf', [status(esa)], [t34_yellow_0])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55          | ~ (l1_orders_2 @ sk_A)
% 0.36/0.55          | ~ (r1_yellow_0 @ sk_A @ X0)
% 0.36/0.55          | ~ (r1_tarski @ X0 @ 
% 0.36/0.55               (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.36/0.55          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.36/0.55             (k1_yellow_0 @ sk_A @ 
% 0.36/0.55              (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.55  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55          | ~ (r1_yellow_0 @ sk_A @ X0)
% 0.36/0.55          | ~ (r1_tarski @ X0 @ 
% 0.36/0.55               (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.36/0.55          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.36/0.55             (k1_yellow_0 @ sk_A @ 
% 0.36/0.55              (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))))),
% 0.36/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.36/0.55         (k1_yellow_0 @ sk_A @ 
% 0.36/0.55          (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))))
% 0.36/0.55        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['16', '30'])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ~ (v5_orders_2 @ sk_A)
% 0.36/0.55        | ~ (v1_yellow_0 @ sk_A)
% 0.36/0.55        | ~ (l1_orders_2 @ sk_A)
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.36/0.55           (k1_yellow_0 @ sk_A @ 
% 0.36/0.55            (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['15', '31'])).
% 0.36/0.55  thf('33', plain, ((v5_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('34', plain, ((v1_yellow_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.36/0.55           (k1_yellow_0 @ sk_A @ 
% 0.36/0.55            (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))))),
% 0.36/0.55      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.36/0.55  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.36/0.55         (k1_yellow_0 @ sk_A @ 
% 0.36/0.55          (k5_waybel_0 @ sk_A @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))))
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.36/0.55      inference('clc', [status(thm)], ['36', '37'])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.36/0.55         (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['14', '38'])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.36/0.55           (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.36/0.55         (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.36/0.55        | ~ (l1_orders_2 @ sk_A)
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['2', '40'])).
% 0.36/0.55  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.36/0.55         (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.36/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.36/0.55  thf('44', plain,
% 0.36/0.55      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.36/0.55         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.36/0.55      inference('split', [status(esa)], ['0'])).
% 0.36/0.55  thf('45', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t4_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.36/0.55       ( m1_subset_1 @ A @ C ) ))).
% 0.36/0.55  thf('46', plain,
% 0.36/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X7 @ X8)
% 0.36/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.36/0.55          | (m1_subset_1 @ X7 @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_subset])).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.55  thf('48', plain,
% 0.36/0.55      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.36/0.55         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['44', '47'])).
% 0.36/0.55  thf('49', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(d20_waybel_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_orders_2 @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.36/0.55             ( ![C:$i]:
% 0.36/0.55               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55                 ( ![D:$i]:
% 0.36/0.55                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.36/0.55                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('50', plain,
% 0.36/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.55          | ~ (v13_waybel_0 @ X16 @ X17)
% 0.36/0.55          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.36/0.55          | (r2_hidden @ X18 @ X16)
% 0.36/0.55          | ~ (r1_orders_2 @ X17 @ X19 @ X18)
% 0.36/0.55          | ~ (r2_hidden @ X19 @ X16)
% 0.36/0.55          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.36/0.55          | ~ (l1_orders_2 @ X17))),
% 0.36/0.55      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.36/0.55  thf('51', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ sk_A)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (r2_hidden @ X0 @ sk_B)
% 0.36/0.55          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.36/0.55          | (r2_hidden @ X1 @ sk_B)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.55  thf('52', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('53', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('54', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (r2_hidden @ X0 @ sk_B)
% 0.36/0.55          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.36/0.55          | (r2_hidden @ X1 @ sk_B)
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.36/0.55  thf('55', plain,
% 0.36/0.55      ((![X0 : $i]:
% 0.36/0.55          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55           | (r2_hidden @ X0 @ sk_B)
% 0.36/0.55           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.36/0.55           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.36/0.55         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['48', '54'])).
% 0.36/0.55  thf('56', plain,
% 0.36/0.55      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.36/0.55         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.36/0.55      inference('split', [status(esa)], ['0'])).
% 0.36/0.55  thf('57', plain,
% 0.36/0.55      ((![X0 : $i]:
% 0.36/0.55          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55           | (r2_hidden @ X0 @ sk_B)
% 0.36/0.55           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.36/0.55         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.36/0.55      inference('demod', [status(thm)], ['55', '56'])).
% 0.36/0.55  thf('58', plain,
% 0.36/0.55      (((((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55         | (r2_hidden @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.36/0.55         | ~ (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.36/0.55              (u1_struct_0 @ sk_A))))
% 0.36/0.55         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['43', '57'])).
% 0.36/0.55  thf('59', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55        | (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.36/0.55           (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.55  thf('60', plain,
% 0.36/0.55      ((((r2_hidden @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.36/0.55         | ((u1_struct_0 @ sk_A) = (sk_B))))
% 0.36/0.55         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.36/0.55      inference('clc', [status(thm)], ['58', '59'])).
% 0.36/0.55  thf('61', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i]:
% 0.36/0.55         (~ (r2_hidden @ (sk_C @ X2 @ X3) @ X2)
% 0.36/0.55          | ((X3) = (X2))
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.36/0.55  thf('62', plain,
% 0.36/0.55      (((((u1_struct_0 @ sk_A) = (sk_B))
% 0.36/0.55         | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55         | ((u1_struct_0 @ sk_A) = (sk_B))))
% 0.36/0.55         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['60', '61'])).
% 0.36/0.55  thf('63', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('64', plain,
% 0.36/0.55      (((((u1_struct_0 @ sk_A) = (sk_B)) | ((u1_struct_0 @ sk_A) = (sk_B))))
% 0.36/0.55         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.36/0.55      inference('demod', [status(thm)], ['62', '63'])).
% 0.36/0.55  thf('65', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (sk_B)))
% 0.36/0.55         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['64'])).
% 0.36/0.55  thf('66', plain,
% 0.36/0.55      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.36/0.55        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('67', plain,
% 0.36/0.55      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.36/0.55         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('split', [status(esa)], ['66'])).
% 0.36/0.55  thf('68', plain,
% 0.36/0.55      (((v1_subset_1 @ sk_B @ sk_B))
% 0.36/0.55         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.36/0.55             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['65', '67'])).
% 0.36/0.55  thf(fc14_subset_1, axiom,
% 0.36/0.55    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.36/0.55  thf('69', plain, (![X4 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X4) @ X4)),
% 0.36/0.55      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.36/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.36/0.55  thf('70', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.55  thf('71', plain, (![X4 : $i]: ~ (v1_subset_1 @ X4 @ X4)),
% 0.36/0.55      inference('demod', [status(thm)], ['69', '70'])).
% 0.36/0.55  thf('72', plain,
% 0.36/0.55      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.36/0.55       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['68', '71'])).
% 0.36/0.55  thf('73', plain,
% 0.36/0.55      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.36/0.55       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('split', [status(esa)], ['66'])).
% 0.36/0.55  thf('74', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(d7_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.36/0.55  thf('75', plain,
% 0.36/0.55      (![X22 : $i, X23 : $i]:
% 0.36/0.55         (((X23) = (X22))
% 0.36/0.55          | (v1_subset_1 @ X23 @ X22)
% 0.36/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.36/0.55  thf('76', plain,
% 0.36/0.55      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['74', '75'])).
% 0.36/0.55  thf('77', plain,
% 0.36/0.55      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.36/0.55         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('split', [status(esa)], ['0'])).
% 0.36/0.55  thf('78', plain,
% 0.36/0.55      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.36/0.55         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['76', '77'])).
% 0.36/0.55  thf(dt_k3_yellow_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_orders_2 @ A ) =>
% 0.36/0.55       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.36/0.55  thf('79', plain,
% 0.36/0.55      (![X11 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (k3_yellow_0 @ X11) @ (u1_struct_0 @ X11))
% 0.36/0.55          | ~ (l1_orders_2 @ X11))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.36/0.55  thf('80', plain,
% 0.36/0.55      ((((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B) | ~ (l1_orders_2 @ sk_A)))
% 0.36/0.55         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('sup+', [status(thm)], ['78', '79'])).
% 0.36/0.55  thf('81', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('82', plain,
% 0.36/0.55      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.36/0.55         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['80', '81'])).
% 0.36/0.55  thf(t2_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.55  thf('83', plain,
% 0.36/0.55      (![X5 : $i, X6 : $i]:
% 0.36/0.55         ((r2_hidden @ X5 @ X6)
% 0.36/0.55          | (v1_xboole_0 @ X6)
% 0.36/0.55          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.55  thf('84', plain,
% 0.36/0.55      ((((v1_xboole_0 @ sk_B) | (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.36/0.55         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['82', '83'])).
% 0.36/0.55  thf('85', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('86', plain,
% 0.36/0.55      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.36/0.55         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('clc', [status(thm)], ['84', '85'])).
% 0.36/0.55  thf('87', plain,
% 0.36/0.55      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.36/0.55         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.36/0.55      inference('split', [status(esa)], ['66'])).
% 0.36/0.55  thf('88', plain,
% 0.36/0.55      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.36/0.55       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['86', '87'])).
% 0.36/0.55  thf('89', plain, ($false),
% 0.36/0.55      inference('sat_resolution*', [status(thm)], ['1', '72', '73', '88'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
