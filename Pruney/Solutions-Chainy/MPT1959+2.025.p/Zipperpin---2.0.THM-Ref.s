%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nfssO7lQs0

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:12 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  252 ( 466 expanded)
%              Number of leaves         :   46 ( 157 expanded)
%              Depth                    :   37
%              Number of atoms          : 2380 (6870 expanded)
%              Number of equality atoms :   44 (  74 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X5 @ X6 ) @ X6 )
      | ( X6 = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('4',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf('5',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( ( k1_yellow_0 @ X29 @ ( k5_waybel_0 @ X29 @ X28 ) )
        = X28 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('6',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_2 ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X17: $i] :
      ( ( ( k3_yellow_0 @ X17 )
        = ( k1_yellow_0 @ X17 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('17',plain,(
    ! [X17: $i] :
      ( ( ( k3_yellow_0 @ X17 )
        = ( k1_yellow_0 @ X17 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf(t42_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( r1_yellow_0 @ A @ k1_xboole_0 )
        & ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X23: $i] :
      ( ( r1_yellow_0 @ X23 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v1_yellow_0 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X23: $i] :
      ( ( r1_yellow_0 @ X23 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v1_yellow_0 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf(t34_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( ( r1_tarski @ B @ C )
            & ( r1_yellow_0 @ A @ B )
            & ( r1_yellow_0 @ A @ C ) )
         => ( r1_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_orders_2 @ X20 @ ( k1_yellow_0 @ X20 @ X21 ) @ ( k1_yellow_0 @ X20 @ X22 ) )
      | ~ ( r1_yellow_0 @ X20 @ X22 )
      | ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_yellow_0 @ X20 @ X21 )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t34_yellow_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ k1_xboole_0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
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
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('33',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('34',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31 = X30 )
      | ( v1_subset_1 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B_1 @ X0 ) @ X0 )
      | ( ( sk_B_1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X8: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['32','37'])).

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

thf('39',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X24 @ X25 ) @ X24 )
      | ( v13_waybel_0 @ X24 @ X25 )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('48',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X24 @ X25 ) @ ( u1_struct_0 @ X25 ) )
      | ( v13_waybel_0 @ X24 @ X25 )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('53',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X24 @ X25 ) @ X24 )
      | ( v13_waybel_0 @ X24 @ X25 )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['46','56'])).

thf('58',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ X1 @ X2 )
      | ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( v13_waybel_0 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['77','80'])).

thf('82',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['67','81'])).

thf('83',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( v13_waybel_0 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['66','82','83'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['57','84'])).

thf('86',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['31','87'])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['16','94'])).

thf('96',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('99',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( ( k1_yellow_0 @ X29 @ ( k5_waybel_0 @ X29 @ X28 ) )
        = X28 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('103',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
        = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
        = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
      = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k3_yellow_0 @ sk_A ) ) )
        = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['15','110'])).

thf('112',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('113',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( ( k1_yellow_0 @ X29 @ ( k5_waybel_0 @ X29 @ X28 ) )
        = X28 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('114',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k3_yellow_0 @ sk_A ) ) )
        = ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k3_yellow_0 @ sk_A ) ) )
        = ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k3_yellow_0 @ sk_A ) ) )
      = ( k3_yellow_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( ( k3_yellow_0 @ sk_A )
      = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['111','121','122'])).

thf('124',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('125',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( ( k1_yellow_0 @ X29 @ ( k5_waybel_0 @ X29 @ X28 ) )
        = X28 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k1_yellow_0 @ X0 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) )
        = ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_yellow_0 @ X0 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X23: $i] :
      ( ( r1_yellow_0 @ X23 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v1_yellow_0 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('129',plain,(
    ! [X4: $i] :
      ( v1_xboole_0 @ ( sk_B @ X4 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('130',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('131',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('132',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['129','134'])).

thf('136',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('137',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( r1_yellow_0 @ X29 @ ( k5_waybel_0 @ X29 @ X28 ) )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_yellow_0 @ X0 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_yellow_0 @ X0 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_orders_2 @ X20 @ ( k1_yellow_0 @ X20 @ X21 ) @ ( k1_yellow_0 @ X20 @ X22 ) )
      | ~ ( r1_yellow_0 @ X20 @ X22 )
      | ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_yellow_0 @ X20 @ X21 )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t34_yellow_0])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( r1_yellow_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( k5_waybel_0 @ X1 @ ( k1_yellow_0 @ X1 @ X0 ) ) )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ X2 ) @ ( k1_yellow_0 @ X1 @ ( k5_waybel_0 @ X1 @ ( k1_yellow_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ X2 ) @ ( k1_yellow_0 @ X1 @ ( k5_waybel_0 @ X1 @ ( k1_yellow_0 @ X1 @ X0 ) ) ) )
      | ~ ( r1_tarski @ X2 @ ( k5_waybel_0 @ X1 @ ( k1_yellow_0 @ X1 @ X0 ) ) )
      | ~ ( r1_yellow_0 @ X1 @ X2 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ ( k5_waybel_0 @ X1 @ ( k1_yellow_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['135','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) ) )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v1_yellow_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['127','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_yellow_0 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
        | ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['123','147'])).

thf('149',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['148','149','150','151','152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ! [X0: $i] :
        ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('158',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
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

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v13_waybel_0 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_2 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['157','163'])).

thf('165',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('166',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_2 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_2 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['156','166'])).

thf('168',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_2 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['14','167'])).

thf('169',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_2 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_2 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_2 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['13','170'])).

thf('172',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X5 @ X6 ) @ X5 )
      | ( X6 = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('173',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_2 )
      | ~ ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_2 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_2 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_2 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_2 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
    | ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['177'])).

thf('179',plain,
    ( ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['176','178'])).

thf('180',plain,(
    ! [X8: $i] :
      ~ ( v1_subset_1 @ ( sk_B_1 @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('182',plain,(
    ! [X8: $i] :
      ~ ( v1_subset_1 @ X8 @ X8 ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
    | ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','182'])).

thf('184',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
    | ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['177'])).

thf('185',plain,(
    ! [X17: $i] :
      ( ( ( k3_yellow_0 @ X17 )
        = ( k1_yellow_0 @ X17 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('186',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31 = X30 )
      | ( v1_subset_1 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('188',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_2
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('190',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('192',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_2 )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['190','191'])).

thf('193',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_2 )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['185','194'])).

thf('196',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('199',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['177'])).

thf('203',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_2 )
    | ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','183','184','203'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nfssO7lQs0
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:17:31 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.18/1.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.18/1.42  % Solved by: fo/fo7.sh
% 1.18/1.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.42  % done 1585 iterations in 0.950s
% 1.18/1.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.18/1.42  % SZS output start Refutation
% 1.18/1.42  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 1.18/1.42  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.42  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.18/1.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.18/1.42  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 1.18/1.42  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 1.18/1.42  thf(sk_B_type, type, sk_B: $i > $i).
% 1.18/1.42  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.18/1.42  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.18/1.42  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 1.18/1.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.18/1.42  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.18/1.42  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.18/1.42  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 1.18/1.42  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.18/1.42  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.18/1.42  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.18/1.42  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.18/1.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.18/1.42  thf(k5_waybel_0_type, type, k5_waybel_0: $i > $i > $i).
% 1.18/1.42  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 1.18/1.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.18/1.42  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.18/1.42  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.18/1.42  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 1.18/1.42  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.18/1.42  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.18/1.42  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.18/1.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.18/1.42  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 1.18/1.42  thf(t8_waybel_7, conjecture,
% 1.18/1.42    (![A:$i]:
% 1.18/1.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.18/1.42         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 1.18/1.42         ( l1_orders_2 @ A ) ) =>
% 1.18/1.42       ( ![B:$i]:
% 1.18/1.42         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 1.18/1.42             ( v13_waybel_0 @ B @ A ) & 
% 1.18/1.42             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.18/1.42           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 1.18/1.42             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 1.18/1.42  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.42    (~( ![A:$i]:
% 1.18/1.42        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.18/1.42            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 1.18/1.42            ( l1_orders_2 @ A ) ) =>
% 1.18/1.42          ( ![B:$i]:
% 1.18/1.42            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 1.18/1.42                ( v13_waybel_0 @ B @ A ) & 
% 1.18/1.42                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.18/1.42              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 1.18/1.42                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 1.18/1.42    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 1.18/1.42  thf('0', plain,
% 1.18/1.42      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)
% 1.18/1.42        | ~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('1', plain,
% 1.18/1.42      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)) | 
% 1.18/1.42       ~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('split', [status(esa)], ['0'])).
% 1.18/1.42  thf('2', plain,
% 1.18/1.42      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf(t49_subset_1, axiom,
% 1.18/1.42    (![A:$i,B:$i]:
% 1.18/1.42     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.18/1.42       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 1.18/1.42         ( ( A ) = ( B ) ) ) ))).
% 1.18/1.42  thf('3', plain,
% 1.18/1.42      (![X5 : $i, X6 : $i]:
% 1.18/1.42         ((m1_subset_1 @ (sk_C_1 @ X5 @ X6) @ X6)
% 1.18/1.42          | ((X6) = (X5))
% 1.18/1.42          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 1.18/1.42      inference('cnf', [status(esa)], [t49_subset_1])).
% 1.18/1.42  thf('4', plain,
% 1.18/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_2))
% 1.18/1.42        | (m1_subset_1 @ (sk_C_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ 
% 1.18/1.42           (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['2', '3'])).
% 1.18/1.42  thf(t34_waybel_0, axiom,
% 1.18/1.42    (![A:$i]:
% 1.18/1.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.18/1.42         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.18/1.42       ( ![B:$i]:
% 1.18/1.42         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.18/1.42           ( ( r1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) ) & 
% 1.18/1.42             ( ( k1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 1.18/1.42  thf('5', plain,
% 1.18/1.42      (![X28 : $i, X29 : $i]:
% 1.18/1.42         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 1.18/1.42          | ((k1_yellow_0 @ X29 @ (k5_waybel_0 @ X29 @ X28)) = (X28))
% 1.18/1.42          | ~ (l1_orders_2 @ X29)
% 1.18/1.42          | ~ (v5_orders_2 @ X29)
% 1.18/1.42          | ~ (v4_orders_2 @ X29)
% 1.18/1.42          | ~ (v3_orders_2 @ X29)
% 1.18/1.42          | (v2_struct_0 @ X29))),
% 1.18/1.42      inference('cnf', [status(esa)], [t34_waybel_0])).
% 1.18/1.42  thf('6', plain,
% 1.18/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_2))
% 1.18/1.42        | (v2_struct_0 @ sk_A)
% 1.18/1.42        | ~ (v3_orders_2 @ sk_A)
% 1.18/1.42        | ~ (v4_orders_2 @ sk_A)
% 1.18/1.42        | ~ (v5_orders_2 @ sk_A)
% 1.18/1.42        | ~ (l1_orders_2 @ sk_A)
% 1.18/1.42        | ((k1_yellow_0 @ sk_A @ 
% 1.18/1.42            (k5_waybel_0 @ sk_A @ (sk_C_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))
% 1.18/1.42            = (sk_C_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.18/1.42      inference('sup-', [status(thm)], ['4', '5'])).
% 1.18/1.42  thf('7', plain, ((v3_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('9', plain, ((v5_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('11', plain,
% 1.18/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_2))
% 1.18/1.42        | (v2_struct_0 @ sk_A)
% 1.18/1.42        | ((k1_yellow_0 @ sk_A @ 
% 1.18/1.42            (k5_waybel_0 @ sk_A @ (sk_C_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))
% 1.18/1.42            = (sk_C_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.18/1.42      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 1.18/1.42  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('13', plain,
% 1.18/1.42      ((((k1_yellow_0 @ sk_A @ 
% 1.18/1.42          (k5_waybel_0 @ sk_A @ (sk_C_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))
% 1.18/1.42          = (sk_C_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 1.18/1.42        | ((u1_struct_0 @ sk_A) = (sk_B_2)))),
% 1.18/1.42      inference('clc', [status(thm)], ['11', '12'])).
% 1.18/1.42  thf(dt_k1_yellow_0, axiom,
% 1.18/1.42    (![A:$i,B:$i]:
% 1.18/1.42     ( ( l1_orders_2 @ A ) =>
% 1.18/1.42       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 1.18/1.42  thf('14', plain,
% 1.18/1.42      (![X18 : $i, X19 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ X18)
% 1.18/1.42          | (m1_subset_1 @ (k1_yellow_0 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 1.18/1.42      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 1.18/1.42  thf(d11_yellow_0, axiom,
% 1.18/1.42    (![A:$i]:
% 1.18/1.42     ( ( l1_orders_2 @ A ) =>
% 1.18/1.42       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 1.18/1.42  thf('15', plain,
% 1.18/1.42      (![X17 : $i]:
% 1.18/1.42         (((k3_yellow_0 @ X17) = (k1_yellow_0 @ X17 @ k1_xboole_0))
% 1.18/1.42          | ~ (l1_orders_2 @ X17))),
% 1.18/1.42      inference('cnf', [status(esa)], [d11_yellow_0])).
% 1.18/1.42  thf('16', plain,
% 1.18/1.42      (![X18 : $i, X19 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ X18)
% 1.18/1.42          | (m1_subset_1 @ (k1_yellow_0 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 1.18/1.42      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 1.18/1.42  thf('17', plain,
% 1.18/1.42      (![X17 : $i]:
% 1.18/1.42         (((k3_yellow_0 @ X17) = (k1_yellow_0 @ X17 @ k1_xboole_0))
% 1.18/1.42          | ~ (l1_orders_2 @ X17))),
% 1.18/1.42      inference('cnf', [status(esa)], [d11_yellow_0])).
% 1.18/1.42  thf(t42_yellow_0, axiom,
% 1.18/1.42    (![A:$i]:
% 1.18/1.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 1.18/1.42         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.18/1.42       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 1.18/1.42         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 1.18/1.42  thf('18', plain,
% 1.18/1.42      (![X23 : $i]:
% 1.18/1.42         ((r1_yellow_0 @ X23 @ k1_xboole_0)
% 1.18/1.42          | ~ (l1_orders_2 @ X23)
% 1.18/1.42          | ~ (v1_yellow_0 @ X23)
% 1.18/1.42          | ~ (v5_orders_2 @ X23)
% 1.18/1.42          | (v2_struct_0 @ X23))),
% 1.18/1.42      inference('cnf', [status(esa)], [t42_yellow_0])).
% 1.18/1.42  thf(d3_tarski, axiom,
% 1.18/1.42    (![A:$i,B:$i]:
% 1.18/1.42     ( ( r1_tarski @ A @ B ) <=>
% 1.18/1.42       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.18/1.42  thf('19', plain,
% 1.18/1.42      (![X1 : $i, X3 : $i]:
% 1.18/1.42         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.18/1.42      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.42  thf('20', plain,
% 1.18/1.42      (![X1 : $i, X3 : $i]:
% 1.18/1.42         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.18/1.42      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.42  thf('21', plain,
% 1.18/1.42      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.18/1.42      inference('sup-', [status(thm)], ['19', '20'])).
% 1.18/1.42  thf('22', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.18/1.42      inference('simplify', [status(thm)], ['21'])).
% 1.18/1.42  thf('23', plain,
% 1.18/1.42      (![X23 : $i]:
% 1.18/1.42         ((r1_yellow_0 @ X23 @ k1_xboole_0)
% 1.18/1.42          | ~ (l1_orders_2 @ X23)
% 1.18/1.42          | ~ (v1_yellow_0 @ X23)
% 1.18/1.42          | ~ (v5_orders_2 @ X23)
% 1.18/1.42          | (v2_struct_0 @ X23))),
% 1.18/1.42      inference('cnf', [status(esa)], [t42_yellow_0])).
% 1.18/1.42  thf(t34_yellow_0, axiom,
% 1.18/1.42    (![A:$i]:
% 1.18/1.42     ( ( l1_orders_2 @ A ) =>
% 1.18/1.42       ( ![B:$i,C:$i]:
% 1.18/1.42         ( ( ( r1_tarski @ B @ C ) & ( r1_yellow_0 @ A @ B ) & 
% 1.18/1.42             ( r1_yellow_0 @ A @ C ) ) =>
% 1.18/1.42           ( r1_orders_2 @
% 1.18/1.42             A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) ))).
% 1.18/1.42  thf('24', plain,
% 1.18/1.42      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.18/1.42         ((r1_orders_2 @ X20 @ (k1_yellow_0 @ X20 @ X21) @ 
% 1.18/1.42           (k1_yellow_0 @ X20 @ X22))
% 1.18/1.42          | ~ (r1_yellow_0 @ X20 @ X22)
% 1.18/1.42          | ~ (r1_tarski @ X21 @ X22)
% 1.18/1.42          | ~ (r1_yellow_0 @ X20 @ X21)
% 1.18/1.42          | ~ (l1_orders_2 @ X20))),
% 1.18/1.42      inference('cnf', [status(esa)], [t34_yellow_0])).
% 1.18/1.42  thf('25', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         ((v2_struct_0 @ X0)
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | ~ (v1_yellow_0 @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | ~ (r1_yellow_0 @ X0 @ X1)
% 1.18/1.42          | ~ (r1_tarski @ X1 @ k1_xboole_0)
% 1.18/1.42          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 1.18/1.42             (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['23', '24'])).
% 1.18/1.42  thf('26', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 1.18/1.42           (k1_yellow_0 @ X0 @ k1_xboole_0))
% 1.18/1.42          | ~ (r1_tarski @ X1 @ k1_xboole_0)
% 1.18/1.42          | ~ (r1_yellow_0 @ X0 @ X1)
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | ~ (v1_yellow_0 @ X0)
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | (v2_struct_0 @ X0))),
% 1.18/1.42      inference('simplify', [status(thm)], ['25'])).
% 1.18/1.42  thf('27', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         ((v2_struct_0 @ X0)
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | ~ (v1_yellow_0 @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | ~ (r1_yellow_0 @ X0 @ k1_xboole_0)
% 1.18/1.42          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 1.18/1.42             (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['22', '26'])).
% 1.18/1.42  thf('28', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         ((v2_struct_0 @ X0)
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | ~ (v1_yellow_0 @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 1.18/1.42             (k1_yellow_0 @ X0 @ k1_xboole_0))
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | ~ (v1_yellow_0 @ X0)
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | (v2_struct_0 @ X0))),
% 1.18/1.42      inference('sup-', [status(thm)], ['18', '27'])).
% 1.18/1.42  thf('29', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 1.18/1.42           (k1_yellow_0 @ X0 @ k1_xboole_0))
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | ~ (v1_yellow_0 @ X0)
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | (v2_struct_0 @ X0))),
% 1.18/1.42      inference('simplify', [status(thm)], ['28'])).
% 1.18/1.42  thf('30', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 1.18/1.42           (k1_yellow_0 @ X0 @ k1_xboole_0))
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | (v2_struct_0 @ X0)
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | ~ (v1_yellow_0 @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0))),
% 1.18/1.42      inference('sup+', [status(thm)], ['17', '29'])).
% 1.18/1.42  thf('31', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         (~ (v1_yellow_0 @ X0)
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | (v2_struct_0 @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 1.18/1.42             (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 1.18/1.42      inference('simplify', [status(thm)], ['30'])).
% 1.18/1.42  thf(rc3_subset_1, axiom,
% 1.18/1.42    (![A:$i]:
% 1.18/1.42     ( ?[B:$i]:
% 1.18/1.42       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 1.18/1.42         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.18/1.42  thf('32', plain,
% 1.18/1.42      (![X8 : $i]: (m1_subset_1 @ (sk_B_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 1.18/1.42      inference('cnf', [status(esa)], [rc3_subset_1])).
% 1.18/1.42  thf('33', plain,
% 1.18/1.42      (![X8 : $i]: (m1_subset_1 @ (sk_B_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 1.18/1.42      inference('cnf', [status(esa)], [rc3_subset_1])).
% 1.18/1.42  thf(d7_subset_1, axiom,
% 1.18/1.42    (![A:$i,B:$i]:
% 1.18/1.42     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.18/1.42       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 1.18/1.42  thf('34', plain,
% 1.18/1.42      (![X30 : $i, X31 : $i]:
% 1.18/1.42         (((X31) = (X30))
% 1.18/1.42          | (v1_subset_1 @ X31 @ X30)
% 1.18/1.42          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 1.18/1.42      inference('cnf', [status(esa)], [d7_subset_1])).
% 1.18/1.42  thf('35', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         ((v1_subset_1 @ (sk_B_1 @ X0) @ X0) | ((sk_B_1 @ X0) = (X0)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['33', '34'])).
% 1.18/1.42  thf('36', plain, (![X8 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X8) @ X8)),
% 1.18/1.42      inference('cnf', [status(esa)], [rc3_subset_1])).
% 1.18/1.42  thf('37', plain, (![X0 : $i]: ((sk_B_1 @ X0) = (X0))),
% 1.18/1.42      inference('clc', [status(thm)], ['35', '36'])).
% 1.18/1.42  thf('38', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 1.18/1.42      inference('demod', [status(thm)], ['32', '37'])).
% 1.18/1.42  thf(d20_waybel_0, axiom,
% 1.18/1.42    (![A:$i]:
% 1.18/1.42     ( ( l1_orders_2 @ A ) =>
% 1.18/1.42       ( ![B:$i]:
% 1.18/1.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.18/1.42           ( ( v13_waybel_0 @ B @ A ) <=>
% 1.18/1.42             ( ![C:$i]:
% 1.18/1.42               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.18/1.42                 ( ![D:$i]:
% 1.18/1.42                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.18/1.42                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 1.18/1.42                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 1.18/1.42  thf('39', plain,
% 1.18/1.42      (![X24 : $i, X25 : $i]:
% 1.18/1.42         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.18/1.42          | (r2_hidden @ (sk_C_2 @ X24 @ X25) @ X24)
% 1.18/1.42          | (v13_waybel_0 @ X24 @ X25)
% 1.18/1.42          | ~ (l1_orders_2 @ X25))),
% 1.18/1.42      inference('cnf', [status(esa)], [d20_waybel_0])).
% 1.18/1.42  thf('40', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ X0)
% 1.18/1.42          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.18/1.42          | (r2_hidden @ (sk_C_2 @ (u1_struct_0 @ X0) @ X0) @ 
% 1.18/1.42             (u1_struct_0 @ X0)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['38', '39'])).
% 1.18/1.42  thf('41', plain,
% 1.18/1.42      (![X8 : $i]: (m1_subset_1 @ (sk_B_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 1.18/1.42      inference('cnf', [status(esa)], [rc3_subset_1])).
% 1.18/1.42  thf(t5_subset, axiom,
% 1.18/1.42    (![A:$i,B:$i,C:$i]:
% 1.18/1.42     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.18/1.42          ( v1_xboole_0 @ C ) ) ))).
% 1.18/1.42  thf('42', plain,
% 1.18/1.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.18/1.42         (~ (r2_hidden @ X14 @ X15)
% 1.18/1.42          | ~ (v1_xboole_0 @ X16)
% 1.18/1.42          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.18/1.42      inference('cnf', [status(esa)], [t5_subset])).
% 1.18/1.42  thf('43', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['41', '42'])).
% 1.18/1.42  thf('44', plain, (![X0 : $i]: ((sk_B_1 @ X0) = (X0))),
% 1.18/1.42      inference('clc', [status(thm)], ['35', '36'])).
% 1.18/1.42  thf('45', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.18/1.42      inference('demod', [status(thm)], ['43', '44'])).
% 1.18/1.42  thf('46', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['40', '45'])).
% 1.18/1.42  thf('47', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 1.18/1.42      inference('demod', [status(thm)], ['32', '37'])).
% 1.18/1.42  thf('48', plain,
% 1.18/1.42      (![X24 : $i, X25 : $i]:
% 1.18/1.42         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.18/1.42          | (m1_subset_1 @ (sk_D @ X24 @ X25) @ (u1_struct_0 @ X25))
% 1.18/1.42          | (v13_waybel_0 @ X24 @ X25)
% 1.18/1.42          | ~ (l1_orders_2 @ X25))),
% 1.18/1.42      inference('cnf', [status(esa)], [d20_waybel_0])).
% 1.18/1.42  thf('49', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ X0)
% 1.18/1.42          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.18/1.42          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0) @ 
% 1.18/1.42             (u1_struct_0 @ X0)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['47', '48'])).
% 1.18/1.42  thf(t2_subset, axiom,
% 1.18/1.42    (![A:$i,B:$i]:
% 1.18/1.42     ( ( m1_subset_1 @ A @ B ) =>
% 1.18/1.42       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.18/1.42  thf('50', plain,
% 1.18/1.42      (![X9 : $i, X10 : $i]:
% 1.18/1.42         ((r2_hidden @ X9 @ X10)
% 1.18/1.42          | (v1_xboole_0 @ X10)
% 1.18/1.42          | ~ (m1_subset_1 @ X9 @ X10))),
% 1.18/1.42      inference('cnf', [status(esa)], [t2_subset])).
% 1.18/1.42  thf('51', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.18/1.42          | (r2_hidden @ (sk_D @ (u1_struct_0 @ X0) @ X0) @ (u1_struct_0 @ X0)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['49', '50'])).
% 1.18/1.42  thf('52', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 1.18/1.42      inference('demod', [status(thm)], ['32', '37'])).
% 1.18/1.42  thf('53', plain,
% 1.18/1.42      (![X24 : $i, X25 : $i]:
% 1.18/1.42         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.18/1.42          | ~ (r2_hidden @ (sk_D @ X24 @ X25) @ X24)
% 1.18/1.42          | (v13_waybel_0 @ X24 @ X25)
% 1.18/1.42          | ~ (l1_orders_2 @ X25))),
% 1.18/1.42      inference('cnf', [status(esa)], [d20_waybel_0])).
% 1.18/1.42  thf('54', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ X0)
% 1.18/1.42          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.18/1.42          | ~ (r2_hidden @ (sk_D @ (u1_struct_0 @ X0) @ X0) @ 
% 1.18/1.42               (u1_struct_0 @ X0)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['52', '53'])).
% 1.18/1.42  thf('55', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.18/1.42          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0))),
% 1.18/1.42      inference('sup-', [status(thm)], ['51', '54'])).
% 1.18/1.42  thf('56', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.18/1.42      inference('simplify', [status(thm)], ['55'])).
% 1.18/1.42  thf('57', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ X0) | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0))),
% 1.18/1.42      inference('clc', [status(thm)], ['46', '56'])).
% 1.18/1.42  thf('58', plain,
% 1.18/1.42      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('split', [status(esa)], ['0'])).
% 1.18/1.42  thf('59', plain,
% 1.18/1.42      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf(t4_subset, axiom,
% 1.18/1.42    (![A:$i,B:$i,C:$i]:
% 1.18/1.42     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.18/1.42       ( m1_subset_1 @ A @ C ) ))).
% 1.18/1.42  thf('60', plain,
% 1.18/1.42      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.18/1.42         (~ (r2_hidden @ X11 @ X12)
% 1.18/1.42          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 1.18/1.42          | (m1_subset_1 @ X11 @ X13))),
% 1.18/1.42      inference('cnf', [status(esa)], [t4_subset])).
% 1.18/1.42  thf('61', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 1.18/1.42      inference('sup-', [status(thm)], ['59', '60'])).
% 1.18/1.42  thf('62', plain,
% 1.18/1.42      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['58', '61'])).
% 1.18/1.42  thf('63', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 1.18/1.42      inference('demod', [status(thm)], ['32', '37'])).
% 1.18/1.42  thf('64', plain,
% 1.18/1.42      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.18/1.42         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.18/1.42          | ~ (v13_waybel_0 @ X24 @ X25)
% 1.18/1.42          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 1.18/1.42          | (r2_hidden @ X26 @ X24)
% 1.18/1.42          | ~ (r1_orders_2 @ X25 @ X27 @ X26)
% 1.18/1.42          | ~ (r2_hidden @ X27 @ X24)
% 1.18/1.42          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 1.18/1.42          | ~ (l1_orders_2 @ X25))),
% 1.18/1.42      inference('cnf', [status(esa)], [d20_waybel_0])).
% 1.18/1.42  thf('65', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ X0)
% 1.18/1.42          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 1.18/1.42          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 1.18/1.42          | ~ (r1_orders_2 @ X0 @ X1 @ X2)
% 1.18/1.42          | (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 1.18/1.42          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.18/1.42          | ~ (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0))),
% 1.18/1.42      inference('sup-', [status(thm)], ['63', '64'])).
% 1.18/1.42  thf('66', plain,
% 1.18/1.42      ((![X0 : $i]:
% 1.18/1.42          (~ (v13_waybel_0 @ (u1_struct_0 @ sk_A) @ sk_A)
% 1.18/1.42           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 1.18/1.42           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.18/1.42           | ~ (l1_orders_2 @ sk_A)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['62', '65'])).
% 1.18/1.42  thf('67', plain,
% 1.18/1.42      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('split', [status(esa)], ['0'])).
% 1.18/1.42  thf('68', plain,
% 1.18/1.42      (![X1 : $i, X3 : $i]:
% 1.18/1.42         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.18/1.42      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.42  thf('69', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 1.18/1.42      inference('sup-', [status(thm)], ['59', '60'])).
% 1.18/1.42  thf('70', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         ((r1_tarski @ sk_B_2 @ X0)
% 1.18/1.42          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_2) @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['68', '69'])).
% 1.18/1.42  thf('71', plain,
% 1.18/1.42      (![X9 : $i, X10 : $i]:
% 1.18/1.42         ((r2_hidden @ X9 @ X10)
% 1.18/1.42          | (v1_xboole_0 @ X10)
% 1.18/1.42          | ~ (m1_subset_1 @ X9 @ X10))),
% 1.18/1.42      inference('cnf', [status(esa)], [t2_subset])).
% 1.18/1.42  thf('72', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         ((r1_tarski @ sk_B_2 @ X0)
% 1.18/1.42          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42          | (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['70', '71'])).
% 1.18/1.42  thf('73', plain,
% 1.18/1.42      (![X1 : $i, X3 : $i]:
% 1.18/1.42         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.18/1.42      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.42  thf('74', plain,
% 1.18/1.42      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42        | (r1_tarski @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 1.18/1.42        | (r1_tarski @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['72', '73'])).
% 1.18/1.42  thf('75', plain,
% 1.18/1.42      (((r1_tarski @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 1.18/1.42        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('simplify', [status(thm)], ['74'])).
% 1.18/1.42  thf('76', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.42         (~ (r2_hidden @ X0 @ X1)
% 1.18/1.42          | (r2_hidden @ X0 @ X2)
% 1.18/1.42          | ~ (r1_tarski @ X1 @ X2))),
% 1.18/1.42      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.42  thf('77', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42          | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 1.18/1.42      inference('sup-', [status(thm)], ['75', '76'])).
% 1.18/1.42  thf('78', plain,
% 1.18/1.42      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('79', plain,
% 1.18/1.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.18/1.42         (~ (r2_hidden @ X14 @ X15)
% 1.18/1.42          | ~ (v1_xboole_0 @ X16)
% 1.18/1.42          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.18/1.42      inference('cnf', [status(esa)], [t5_subset])).
% 1.18/1.42  thf('80', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 1.18/1.42      inference('sup-', [status(thm)], ['78', '79'])).
% 1.18/1.42  thf('81', plain,
% 1.18/1.42      (![X0 : $i]:
% 1.18/1.42         (~ (r2_hidden @ X0 @ sk_B_2) | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('clc', [status(thm)], ['77', '80'])).
% 1.18/1.42  thf('82', plain,
% 1.18/1.42      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['67', '81'])).
% 1.18/1.42  thf('83', plain, ((l1_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('84', plain,
% 1.18/1.42      ((![X0 : $i]:
% 1.18/1.42          (~ (v13_waybel_0 @ (u1_struct_0 @ sk_A) @ sk_A)
% 1.18/1.42           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('demod', [status(thm)], ['66', '82', '83'])).
% 1.18/1.42  thf('85', plain,
% 1.18/1.42      ((![X0 : $i]:
% 1.18/1.42          (~ (l1_orders_2 @ sk_A)
% 1.18/1.42           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 1.18/1.42           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['57', '84'])).
% 1.18/1.42  thf('86', plain, ((l1_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('87', plain,
% 1.18/1.42      ((![X0 : $i]:
% 1.18/1.42          (~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 1.18/1.42           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('demod', [status(thm)], ['85', '86'])).
% 1.18/1.42  thf('88', plain,
% 1.18/1.42      (((~ (l1_orders_2 @ sk_A)
% 1.18/1.42         | (v2_struct_0 @ sk_A)
% 1.18/1.42         | ~ (v5_orders_2 @ sk_A)
% 1.18/1.42         | ~ (v1_yellow_0 @ sk_A)
% 1.18/1.42         | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 1.18/1.42              (u1_struct_0 @ sk_A))
% 1.18/1.42         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 1.18/1.42            (u1_struct_0 @ sk_A))))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['31', '87'])).
% 1.18/1.42  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('90', plain, ((v5_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('91', plain, ((v1_yellow_0 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('92', plain,
% 1.18/1.42      ((((v2_struct_0 @ sk_A)
% 1.18/1.42         | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 1.18/1.42              (u1_struct_0 @ sk_A))
% 1.18/1.42         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 1.18/1.42            (u1_struct_0 @ sk_A))))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 1.18/1.42  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('94', plain,
% 1.18/1.42      ((((r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ (u1_struct_0 @ sk_A))
% 1.18/1.42         | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 1.18/1.42              (u1_struct_0 @ sk_A))))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('clc', [status(thm)], ['92', '93'])).
% 1.18/1.42  thf('95', plain,
% 1.18/1.42      (((~ (l1_orders_2 @ sk_A)
% 1.18/1.42         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 1.18/1.42            (u1_struct_0 @ sk_A))))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['16', '94'])).
% 1.18/1.42  thf('96', plain, ((l1_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('97', plain,
% 1.18/1.42      (((r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ (u1_struct_0 @ sk_A)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('demod', [status(thm)], ['95', '96'])).
% 1.18/1.42  thf('98', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 1.18/1.42      inference('demod', [status(thm)], ['32', '37'])).
% 1.18/1.42  thf('99', plain,
% 1.18/1.42      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.18/1.42         (~ (r2_hidden @ X11 @ X12)
% 1.18/1.42          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 1.18/1.42          | (m1_subset_1 @ X11 @ X13))),
% 1.18/1.42      inference('cnf', [status(esa)], [t4_subset])).
% 1.18/1.42  thf('100', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.18/1.42      inference('sup-', [status(thm)], ['98', '99'])).
% 1.18/1.42  thf('101', plain,
% 1.18/1.42      (((m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 1.18/1.42         (u1_struct_0 @ sk_A)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['97', '100'])).
% 1.18/1.42  thf('102', plain,
% 1.18/1.42      (![X28 : $i, X29 : $i]:
% 1.18/1.42         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 1.18/1.42          | ((k1_yellow_0 @ X29 @ (k5_waybel_0 @ X29 @ X28)) = (X28))
% 1.18/1.42          | ~ (l1_orders_2 @ X29)
% 1.18/1.42          | ~ (v5_orders_2 @ X29)
% 1.18/1.42          | ~ (v4_orders_2 @ X29)
% 1.18/1.42          | ~ (v3_orders_2 @ X29)
% 1.18/1.42          | (v2_struct_0 @ X29))),
% 1.18/1.42      inference('cnf', [status(esa)], [t34_waybel_0])).
% 1.18/1.42  thf('103', plain,
% 1.18/1.42      ((((v2_struct_0 @ sk_A)
% 1.18/1.42         | ~ (v3_orders_2 @ sk_A)
% 1.18/1.42         | ~ (v4_orders_2 @ sk_A)
% 1.18/1.42         | ~ (v5_orders_2 @ sk_A)
% 1.18/1.42         | ~ (l1_orders_2 @ sk_A)
% 1.18/1.42         | ((k1_yellow_0 @ sk_A @ 
% 1.18/1.42             (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 1.18/1.42             = (k1_yellow_0 @ sk_A @ k1_xboole_0))))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['101', '102'])).
% 1.18/1.42  thf('104', plain, ((v3_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('105', plain, ((v4_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('106', plain, ((v5_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('107', plain, ((l1_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('108', plain,
% 1.18/1.42      ((((v2_struct_0 @ sk_A)
% 1.18/1.42         | ((k1_yellow_0 @ sk_A @ 
% 1.18/1.42             (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 1.18/1.42             = (k1_yellow_0 @ sk_A @ k1_xboole_0))))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 1.18/1.42  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('110', plain,
% 1.18/1.42      ((((k1_yellow_0 @ sk_A @ 
% 1.18/1.42          (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 1.18/1.42          = (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('clc', [status(thm)], ['108', '109'])).
% 1.18/1.42  thf('111', plain,
% 1.18/1.42      (((((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ (k3_yellow_0 @ sk_A)))
% 1.18/1.42           = (k1_yellow_0 @ sk_A @ k1_xboole_0))
% 1.18/1.42         | ~ (l1_orders_2 @ sk_A)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup+', [status(thm)], ['15', '110'])).
% 1.18/1.42  thf('112', plain,
% 1.18/1.42      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['58', '61'])).
% 1.18/1.42  thf('113', plain,
% 1.18/1.42      (![X28 : $i, X29 : $i]:
% 1.18/1.42         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 1.18/1.42          | ((k1_yellow_0 @ X29 @ (k5_waybel_0 @ X29 @ X28)) = (X28))
% 1.18/1.42          | ~ (l1_orders_2 @ X29)
% 1.18/1.42          | ~ (v5_orders_2 @ X29)
% 1.18/1.42          | ~ (v4_orders_2 @ X29)
% 1.18/1.42          | ~ (v3_orders_2 @ X29)
% 1.18/1.42          | (v2_struct_0 @ X29))),
% 1.18/1.42      inference('cnf', [status(esa)], [t34_waybel_0])).
% 1.18/1.42  thf('114', plain,
% 1.18/1.42      ((((v2_struct_0 @ sk_A)
% 1.18/1.42         | ~ (v3_orders_2 @ sk_A)
% 1.18/1.42         | ~ (v4_orders_2 @ sk_A)
% 1.18/1.42         | ~ (v5_orders_2 @ sk_A)
% 1.18/1.42         | ~ (l1_orders_2 @ sk_A)
% 1.18/1.42         | ((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ (k3_yellow_0 @ sk_A)))
% 1.18/1.42             = (k3_yellow_0 @ sk_A))))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['112', '113'])).
% 1.18/1.42  thf('115', plain, ((v3_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('116', plain, ((v4_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('117', plain, ((v5_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('118', plain, ((l1_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('119', plain,
% 1.18/1.42      ((((v2_struct_0 @ sk_A)
% 1.18/1.42         | ((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ (k3_yellow_0 @ sk_A)))
% 1.18/1.42             = (k3_yellow_0 @ sk_A))))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 1.18/1.42  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('121', plain,
% 1.18/1.42      ((((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ (k3_yellow_0 @ sk_A)))
% 1.18/1.42          = (k3_yellow_0 @ sk_A)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('clc', [status(thm)], ['119', '120'])).
% 1.18/1.42  thf('122', plain, ((l1_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('123', plain,
% 1.18/1.42      ((((k3_yellow_0 @ sk_A) = (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('demod', [status(thm)], ['111', '121', '122'])).
% 1.18/1.42  thf('124', plain,
% 1.18/1.42      (![X18 : $i, X19 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ X18)
% 1.18/1.42          | (m1_subset_1 @ (k1_yellow_0 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 1.18/1.42      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 1.18/1.42  thf('125', plain,
% 1.18/1.42      (![X28 : $i, X29 : $i]:
% 1.18/1.42         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 1.18/1.42          | ((k1_yellow_0 @ X29 @ (k5_waybel_0 @ X29 @ X28)) = (X28))
% 1.18/1.42          | ~ (l1_orders_2 @ X29)
% 1.18/1.42          | ~ (v5_orders_2 @ X29)
% 1.18/1.42          | ~ (v4_orders_2 @ X29)
% 1.18/1.42          | ~ (v3_orders_2 @ X29)
% 1.18/1.42          | (v2_struct_0 @ X29))),
% 1.18/1.42      inference('cnf', [status(esa)], [t34_waybel_0])).
% 1.18/1.42  thf('126', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ X0)
% 1.18/1.42          | (v2_struct_0 @ X0)
% 1.18/1.42          | ~ (v3_orders_2 @ X0)
% 1.18/1.42          | ~ (v4_orders_2 @ X0)
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | ((k1_yellow_0 @ X0 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1)))
% 1.18/1.42              = (k1_yellow_0 @ X0 @ X1)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['124', '125'])).
% 1.18/1.42  thf('127', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         (((k1_yellow_0 @ X0 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1)))
% 1.18/1.42            = (k1_yellow_0 @ X0 @ X1))
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | ~ (v4_orders_2 @ X0)
% 1.18/1.42          | ~ (v3_orders_2 @ X0)
% 1.18/1.42          | (v2_struct_0 @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0))),
% 1.18/1.42      inference('simplify', [status(thm)], ['126'])).
% 1.18/1.42  thf('128', plain,
% 1.18/1.42      (![X23 : $i]:
% 1.18/1.42         ((r1_yellow_0 @ X23 @ k1_xboole_0)
% 1.18/1.42          | ~ (l1_orders_2 @ X23)
% 1.18/1.42          | ~ (v1_yellow_0 @ X23)
% 1.18/1.42          | ~ (v5_orders_2 @ X23)
% 1.18/1.42          | (v2_struct_0 @ X23))),
% 1.18/1.42      inference('cnf', [status(esa)], [t42_yellow_0])).
% 1.18/1.42  thf(rc2_subset_1, axiom,
% 1.18/1.42    (![A:$i]:
% 1.18/1.42     ( ?[B:$i]:
% 1.18/1.42       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.18/1.42  thf('129', plain, (![X4 : $i]: (v1_xboole_0 @ (sk_B @ X4))),
% 1.18/1.42      inference('cnf', [status(esa)], [rc2_subset_1])).
% 1.18/1.42  thf('130', plain,
% 1.18/1.42      (![X1 : $i, X3 : $i]:
% 1.18/1.42         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.18/1.42      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.42  thf(t4_subset_1, axiom,
% 1.18/1.42    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.18/1.42  thf('131', plain,
% 1.18/1.42      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.18/1.42      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.18/1.42  thf('132', plain,
% 1.18/1.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.18/1.42         (~ (r2_hidden @ X14 @ X15)
% 1.18/1.42          | ~ (v1_xboole_0 @ X16)
% 1.18/1.42          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.18/1.42      inference('cnf', [status(esa)], [t5_subset])).
% 1.18/1.42  thf('133', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.18/1.42      inference('sup-', [status(thm)], ['131', '132'])).
% 1.18/1.42  thf('134', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.18/1.42      inference('sup-', [status(thm)], ['130', '133'])).
% 1.18/1.42  thf('135', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 1.18/1.42      inference('sup-', [status(thm)], ['129', '134'])).
% 1.18/1.42  thf('136', plain,
% 1.18/1.42      (![X18 : $i, X19 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ X18)
% 1.18/1.42          | (m1_subset_1 @ (k1_yellow_0 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 1.18/1.42      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 1.18/1.42  thf('137', plain,
% 1.18/1.42      (![X28 : $i, X29 : $i]:
% 1.18/1.42         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 1.18/1.42          | (r1_yellow_0 @ X29 @ (k5_waybel_0 @ X29 @ X28))
% 1.18/1.42          | ~ (l1_orders_2 @ X29)
% 1.18/1.42          | ~ (v5_orders_2 @ X29)
% 1.18/1.42          | ~ (v4_orders_2 @ X29)
% 1.18/1.42          | ~ (v3_orders_2 @ X29)
% 1.18/1.42          | (v2_struct_0 @ X29))),
% 1.18/1.42      inference('cnf', [status(esa)], [t34_waybel_0])).
% 1.18/1.42  thf('138', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ X0)
% 1.18/1.42          | (v2_struct_0 @ X0)
% 1.18/1.42          | ~ (v3_orders_2 @ X0)
% 1.18/1.42          | ~ (v4_orders_2 @ X0)
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | (r1_yellow_0 @ X0 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1))))),
% 1.18/1.42      inference('sup-', [status(thm)], ['136', '137'])).
% 1.18/1.42  thf('139', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         ((r1_yellow_0 @ X0 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1)))
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | ~ (v4_orders_2 @ X0)
% 1.18/1.42          | ~ (v3_orders_2 @ X0)
% 1.18/1.42          | (v2_struct_0 @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0))),
% 1.18/1.42      inference('simplify', [status(thm)], ['138'])).
% 1.18/1.42  thf('140', plain,
% 1.18/1.42      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.18/1.42         ((r1_orders_2 @ X20 @ (k1_yellow_0 @ X20 @ X21) @ 
% 1.18/1.42           (k1_yellow_0 @ X20 @ X22))
% 1.18/1.42          | ~ (r1_yellow_0 @ X20 @ X22)
% 1.18/1.42          | ~ (r1_tarski @ X21 @ X22)
% 1.18/1.42          | ~ (r1_yellow_0 @ X20 @ X21)
% 1.18/1.42          | ~ (l1_orders_2 @ X20))),
% 1.18/1.42      inference('cnf', [status(esa)], [t34_yellow_0])).
% 1.18/1.42  thf('141', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ X1)
% 1.18/1.42          | (v2_struct_0 @ X1)
% 1.18/1.42          | ~ (v3_orders_2 @ X1)
% 1.18/1.42          | ~ (v4_orders_2 @ X1)
% 1.18/1.42          | ~ (v5_orders_2 @ X1)
% 1.18/1.42          | ~ (l1_orders_2 @ X1)
% 1.18/1.42          | ~ (r1_yellow_0 @ X1 @ X2)
% 1.18/1.42          | ~ (r1_tarski @ X2 @ (k5_waybel_0 @ X1 @ (k1_yellow_0 @ X1 @ X0)))
% 1.18/1.42          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ X2) @ 
% 1.18/1.42             (k1_yellow_0 @ X1 @ (k5_waybel_0 @ X1 @ (k1_yellow_0 @ X1 @ X0)))))),
% 1.18/1.42      inference('sup-', [status(thm)], ['139', '140'])).
% 1.18/1.42  thf('142', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.42         ((r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ X2) @ 
% 1.18/1.42           (k1_yellow_0 @ X1 @ (k5_waybel_0 @ X1 @ (k1_yellow_0 @ X1 @ X0))))
% 1.18/1.42          | ~ (r1_tarski @ X2 @ (k5_waybel_0 @ X1 @ (k1_yellow_0 @ X1 @ X0)))
% 1.18/1.42          | ~ (r1_yellow_0 @ X1 @ X2)
% 1.18/1.42          | ~ (v5_orders_2 @ X1)
% 1.18/1.42          | ~ (v4_orders_2 @ X1)
% 1.18/1.42          | ~ (v3_orders_2 @ X1)
% 1.18/1.42          | (v2_struct_0 @ X1)
% 1.18/1.42          | ~ (l1_orders_2 @ X1))),
% 1.18/1.42      inference('simplify', [status(thm)], ['141'])).
% 1.18/1.42  thf('143', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ X1)
% 1.18/1.42          | (v2_struct_0 @ X1)
% 1.18/1.42          | ~ (v3_orders_2 @ X1)
% 1.18/1.42          | ~ (v4_orders_2 @ X1)
% 1.18/1.42          | ~ (v5_orders_2 @ X1)
% 1.18/1.42          | ~ (r1_yellow_0 @ X1 @ k1_xboole_0)
% 1.18/1.42          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 1.18/1.42             (k1_yellow_0 @ X1 @ (k5_waybel_0 @ X1 @ (k1_yellow_0 @ X1 @ X0)))))),
% 1.18/1.42      inference('sup-', [status(thm)], ['135', '142'])).
% 1.18/1.42  thf('144', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         ((v2_struct_0 @ X0)
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | ~ (v1_yellow_0 @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 1.18/1.42             (k1_yellow_0 @ X0 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1))))
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | ~ (v4_orders_2 @ X0)
% 1.18/1.42          | ~ (v3_orders_2 @ X0)
% 1.18/1.42          | (v2_struct_0 @ X0)
% 1.18/1.42          | ~ (l1_orders_2 @ X0))),
% 1.18/1.42      inference('sup-', [status(thm)], ['128', '143'])).
% 1.18/1.42  thf('145', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         (~ (v3_orders_2 @ X0)
% 1.18/1.42          | ~ (v4_orders_2 @ X0)
% 1.18/1.42          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 1.18/1.42             (k1_yellow_0 @ X0 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1))))
% 1.18/1.42          | ~ (l1_orders_2 @ X0)
% 1.18/1.42          | ~ (v1_yellow_0 @ X0)
% 1.18/1.42          | ~ (v5_orders_2 @ X0)
% 1.18/1.42          | (v2_struct_0 @ X0))),
% 1.18/1.42      inference('simplify', [status(thm)], ['144'])).
% 1.18/1.42  thf('146', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         ((r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 1.18/1.42           (k1_yellow_0 @ X1 @ X0))
% 1.18/1.42          | ~ (l1_orders_2 @ X1)
% 1.18/1.42          | (v2_struct_0 @ X1)
% 1.18/1.42          | ~ (v3_orders_2 @ X1)
% 1.18/1.42          | ~ (v4_orders_2 @ X1)
% 1.18/1.42          | ~ (v5_orders_2 @ X1)
% 1.18/1.42          | (v2_struct_0 @ X1)
% 1.18/1.42          | ~ (v5_orders_2 @ X1)
% 1.18/1.42          | ~ (v1_yellow_0 @ X1)
% 1.18/1.42          | ~ (l1_orders_2 @ X1)
% 1.18/1.42          | ~ (v4_orders_2 @ X1)
% 1.18/1.42          | ~ (v3_orders_2 @ X1))),
% 1.18/1.42      inference('sup+', [status(thm)], ['127', '145'])).
% 1.18/1.42  thf('147', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         (~ (v1_yellow_0 @ X1)
% 1.18/1.42          | ~ (v5_orders_2 @ X1)
% 1.18/1.42          | ~ (v4_orders_2 @ X1)
% 1.18/1.42          | ~ (v3_orders_2 @ X1)
% 1.18/1.42          | (v2_struct_0 @ X1)
% 1.18/1.42          | ~ (l1_orders_2 @ X1)
% 1.18/1.42          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 1.18/1.42             (k1_yellow_0 @ X1 @ X0)))),
% 1.18/1.42      inference('simplify', [status(thm)], ['146'])).
% 1.18/1.42  thf('148', plain,
% 1.18/1.42      ((![X0 : $i]:
% 1.18/1.42          ((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 1.18/1.42            (k1_yellow_0 @ sk_A @ X0))
% 1.18/1.42           | ~ (l1_orders_2 @ sk_A)
% 1.18/1.42           | (v2_struct_0 @ sk_A)
% 1.18/1.42           | ~ (v3_orders_2 @ sk_A)
% 1.18/1.42           | ~ (v4_orders_2 @ sk_A)
% 1.18/1.42           | ~ (v5_orders_2 @ sk_A)
% 1.18/1.42           | ~ (v1_yellow_0 @ sk_A)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup+', [status(thm)], ['123', '147'])).
% 1.18/1.42  thf('149', plain, ((l1_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('150', plain, ((v3_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('151', plain, ((v4_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('152', plain, ((v5_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('153', plain, ((v1_yellow_0 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('154', plain,
% 1.18/1.42      ((![X0 : $i]:
% 1.18/1.42          ((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 1.18/1.42            (k1_yellow_0 @ sk_A @ X0))
% 1.18/1.42           | (v2_struct_0 @ sk_A)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('demod', [status(thm)],
% 1.18/1.42                ['148', '149', '150', '151', '152', '153'])).
% 1.18/1.42  thf('155', plain, (~ (v2_struct_0 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('156', plain,
% 1.18/1.42      ((![X0 : $i]:
% 1.18/1.42          (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 1.18/1.42           (k1_yellow_0 @ sk_A @ X0)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('clc', [status(thm)], ['154', '155'])).
% 1.18/1.42  thf('157', plain,
% 1.18/1.42      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['58', '61'])).
% 1.18/1.42  thf('158', plain,
% 1.18/1.42      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('159', plain,
% 1.18/1.42      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.18/1.42         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.18/1.42          | ~ (v13_waybel_0 @ X24 @ X25)
% 1.18/1.42          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 1.18/1.42          | (r2_hidden @ X26 @ X24)
% 1.18/1.42          | ~ (r1_orders_2 @ X25 @ X27 @ X26)
% 1.18/1.42          | ~ (r2_hidden @ X27 @ X24)
% 1.18/1.42          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 1.18/1.42          | ~ (l1_orders_2 @ X25))),
% 1.18/1.42      inference('cnf', [status(esa)], [d20_waybel_0])).
% 1.18/1.42  thf('160', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ sk_A)
% 1.18/1.42          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42          | ~ (r2_hidden @ X0 @ sk_B_2)
% 1.18/1.42          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 1.18/1.42          | (r2_hidden @ X1 @ sk_B_2)
% 1.18/1.42          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.18/1.42          | ~ (v13_waybel_0 @ sk_B_2 @ sk_A))),
% 1.18/1.42      inference('sup-', [status(thm)], ['158', '159'])).
% 1.18/1.42  thf('161', plain, ((l1_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('162', plain, ((v13_waybel_0 @ sk_B_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('163', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i]:
% 1.18/1.42         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42          | ~ (r2_hidden @ X0 @ sk_B_2)
% 1.18/1.42          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 1.18/1.42          | (r2_hidden @ X1 @ sk_B_2)
% 1.18/1.42          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('demod', [status(thm)], ['160', '161', '162'])).
% 1.18/1.42  thf('164', plain,
% 1.18/1.42      ((![X0 : $i]:
% 1.18/1.42          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42           | (r2_hidden @ X0 @ sk_B_2)
% 1.18/1.42           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 1.18/1.42           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['157', '163'])).
% 1.18/1.42  thf('165', plain,
% 1.18/1.42      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('split', [status(esa)], ['0'])).
% 1.18/1.42  thf('166', plain,
% 1.18/1.42      ((![X0 : $i]:
% 1.18/1.42          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.18/1.42           | (r2_hidden @ X0 @ sk_B_2)
% 1.18/1.42           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('demod', [status(thm)], ['164', '165'])).
% 1.18/1.42  thf('167', plain,
% 1.18/1.42      ((![X0 : $i]:
% 1.18/1.42          ((r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_2)
% 1.18/1.42           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['156', '166'])).
% 1.18/1.42  thf('168', plain,
% 1.18/1.42      ((![X0 : $i]:
% 1.18/1.42          (~ (l1_orders_2 @ sk_A)
% 1.18/1.42           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_2)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['14', '167'])).
% 1.18/1.42  thf('169', plain, ((l1_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('170', plain,
% 1.18/1.42      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_2))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('demod', [status(thm)], ['168', '169'])).
% 1.18/1.42  thf('171', plain,
% 1.18/1.42      ((((r2_hidden @ (sk_C_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ sk_B_2)
% 1.18/1.42         | ((u1_struct_0 @ sk_A) = (sk_B_2))))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup+', [status(thm)], ['13', '170'])).
% 1.18/1.42  thf('172', plain,
% 1.18/1.42      (![X5 : $i, X6 : $i]:
% 1.18/1.42         (~ (r2_hidden @ (sk_C_1 @ X5 @ X6) @ X5)
% 1.18/1.42          | ((X6) = (X5))
% 1.18/1.42          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 1.18/1.42      inference('cnf', [status(esa)], [t49_subset_1])).
% 1.18/1.42  thf('173', plain,
% 1.18/1.42      (((((u1_struct_0 @ sk_A) = (sk_B_2))
% 1.18/1.42         | ~ (m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.18/1.42         | ((u1_struct_0 @ sk_A) = (sk_B_2))))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['171', '172'])).
% 1.18/1.42  thf('174', plain,
% 1.18/1.42      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('175', plain,
% 1.18/1.42      (((((u1_struct_0 @ sk_A) = (sk_B_2)) | ((u1_struct_0 @ sk_A) = (sk_B_2))))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('demod', [status(thm)], ['173', '174'])).
% 1.18/1.42  thf('176', plain,
% 1.18/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_2)))
% 1.18/1.42         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('simplify', [status(thm)], ['175'])).
% 1.18/1.42  thf('177', plain,
% 1.18/1.42      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)
% 1.18/1.42        | (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('178', plain,
% 1.18/1.42      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 1.18/1.42         <= (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.18/1.42      inference('split', [status(esa)], ['177'])).
% 1.18/1.42  thf('179', plain,
% 1.18/1.42      (((v1_subset_1 @ sk_B_2 @ sk_B_2))
% 1.18/1.42         <= (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 1.18/1.42             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('sup+', [status(thm)], ['176', '178'])).
% 1.18/1.42  thf('180', plain, (![X8 : $i]: ~ (v1_subset_1 @ (sk_B_1 @ X8) @ X8)),
% 1.18/1.42      inference('cnf', [status(esa)], [rc3_subset_1])).
% 1.18/1.42  thf('181', plain, (![X0 : $i]: ((sk_B_1 @ X0) = (X0))),
% 1.18/1.42      inference('clc', [status(thm)], ['35', '36'])).
% 1.18/1.42  thf('182', plain, (![X8 : $i]: ~ (v1_subset_1 @ X8 @ X8)),
% 1.18/1.42      inference('demod', [status(thm)], ['180', '181'])).
% 1.18/1.42  thf('183', plain,
% 1.18/1.42      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)) | 
% 1.18/1.42       ~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['179', '182'])).
% 1.18/1.42  thf('184', plain,
% 1.18/1.42      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)) | 
% 1.18/1.42       ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('split', [status(esa)], ['177'])).
% 1.18/1.42  thf('185', plain,
% 1.18/1.42      (![X17 : $i]:
% 1.18/1.42         (((k3_yellow_0 @ X17) = (k1_yellow_0 @ X17 @ k1_xboole_0))
% 1.18/1.42          | ~ (l1_orders_2 @ X17))),
% 1.18/1.42      inference('cnf', [status(esa)], [d11_yellow_0])).
% 1.18/1.42  thf('186', plain,
% 1.18/1.42      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('187', plain,
% 1.18/1.42      (![X30 : $i, X31 : $i]:
% 1.18/1.42         (((X31) = (X30))
% 1.18/1.42          | (v1_subset_1 @ X31 @ X30)
% 1.18/1.42          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 1.18/1.42      inference('cnf', [status(esa)], [d7_subset_1])).
% 1.18/1.42  thf('188', plain,
% 1.18/1.42      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 1.18/1.42        | ((sk_B_2) = (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['186', '187'])).
% 1.18/1.42  thf('189', plain,
% 1.18/1.42      ((~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 1.18/1.42         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.18/1.42      inference('split', [status(esa)], ['0'])).
% 1.18/1.42  thf('190', plain,
% 1.18/1.42      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 1.18/1.42         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.18/1.42      inference('sup-', [status(thm)], ['188', '189'])).
% 1.18/1.42  thf('191', plain,
% 1.18/1.42      (![X18 : $i, X19 : $i]:
% 1.18/1.42         (~ (l1_orders_2 @ X18)
% 1.18/1.42          | (m1_subset_1 @ (k1_yellow_0 @ X18 @ X19) @ (u1_struct_0 @ X18)))),
% 1.18/1.42      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 1.18/1.42  thf('192', plain,
% 1.18/1.42      ((![X0 : $i]:
% 1.18/1.42          ((m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_2)
% 1.18/1.42           | ~ (l1_orders_2 @ sk_A)))
% 1.18/1.42         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.18/1.42      inference('sup+', [status(thm)], ['190', '191'])).
% 1.18/1.42  thf('193', plain, ((l1_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('194', plain,
% 1.18/1.42      ((![X0 : $i]: (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_2))
% 1.18/1.42         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.18/1.42      inference('demod', [status(thm)], ['192', '193'])).
% 1.18/1.42  thf('195', plain,
% 1.18/1.42      ((((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_2) | ~ (l1_orders_2 @ sk_A)))
% 1.18/1.42         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.18/1.42      inference('sup+', [status(thm)], ['185', '194'])).
% 1.18/1.42  thf('196', plain, ((l1_orders_2 @ sk_A)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('197', plain,
% 1.18/1.42      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B_2))
% 1.18/1.42         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.18/1.42      inference('demod', [status(thm)], ['195', '196'])).
% 1.18/1.42  thf('198', plain,
% 1.18/1.42      (![X9 : $i, X10 : $i]:
% 1.18/1.42         ((r2_hidden @ X9 @ X10)
% 1.18/1.42          | (v1_xboole_0 @ X10)
% 1.18/1.42          | ~ (m1_subset_1 @ X9 @ X10))),
% 1.18/1.42      inference('cnf', [status(esa)], [t2_subset])).
% 1.18/1.42  thf('199', plain,
% 1.18/1.42      ((((v1_xboole_0 @ sk_B_2) | (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))
% 1.18/1.42         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.18/1.42      inference('sup-', [status(thm)], ['197', '198'])).
% 1.18/1.42  thf('200', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('201', plain,
% 1.18/1.42      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2))
% 1.18/1.42         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.18/1.42      inference('clc', [status(thm)], ['199', '200'])).
% 1.18/1.42  thf('202', plain,
% 1.18/1.42      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2))
% 1.18/1.42         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)))),
% 1.18/1.42      inference('split', [status(esa)], ['177'])).
% 1.18/1.42  thf('203', plain,
% 1.18/1.42      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_2)) | 
% 1.18/1.42       ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['201', '202'])).
% 1.18/1.42  thf('204', plain, ($false),
% 1.18/1.42      inference('sat_resolution*', [status(thm)], ['1', '183', '184', '203'])).
% 1.18/1.42  
% 1.18/1.42  % SZS output end Refutation
% 1.18/1.42  
% 1.18/1.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
