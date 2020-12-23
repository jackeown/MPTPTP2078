%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zjhHJHCV87

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:13 EST 2020

% Result     : Theorem 3.24s
% Output     : Refutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 777 expanded)
%              Number of leaves         :   45 ( 236 expanded)
%              Depth                    :   36
%              Number of atoms          : 2152 (12313 expanded)
%              Number of equality atoms :   39 (  90 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

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
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t42_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( r1_yellow_0 @ A @ k1_xboole_0 )
        & ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X32: $i] :
      ( ( r1_yellow_0 @ X32 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X32 )
      | ~ ( v1_yellow_0 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('8',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('9',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38 = X37 )
      | ( v1_subset_1 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['7','12'])).

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

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( X6 = X4 )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X6 @ X5 ) @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf(d9_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r2_hidden @ ( sk_D_1 @ X20 @ X22 @ X21 ) @ X22 )
      | ( r2_lattice3 @ X21 @ X22 @ X20 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('25',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d9_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_yellow_0 @ A @ B )
           => ( ( C
                = ( k1_yellow_0 @ A @ B ) )
            <=> ( ( r2_lattice3 @ A @ B @ C )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                     => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X27
       != ( k1_yellow_0 @ X25 @ X26 ) )
      | ~ ( r2_lattice3 @ X25 @ X26 @ X28 )
      | ( r1_orders_2 @ X25 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r1_yellow_0 @ X25 @ X26 )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('27',plain,(
    ! [X25: $i,X26: $i,X28: $i] :
      ( ~ ( l1_orders_2 @ X25 )
      | ~ ( r1_yellow_0 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X25 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X25 ) )
      | ( r1_orders_2 @ X25 @ ( k1_yellow_0 @ X25 @ X26 ) @ X28 )
      | ~ ( r2_lattice3 @ X25 @ X26 @ X28 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','34'])).

thf('36',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('43',plain,(
    ! [X32: $i] :
      ( ( r1_yellow_0 @ X32 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X32 )
      | ~ ( v1_yellow_0 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('45',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('46',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r2_hidden @ ( sk_D_1 @ X20 @ X22 @ X21 ) @ X22 )
      | ( r2_lattice3 @ X21 @ X22 @ X20 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( r2_lattice3 @ X1 @ X0 @ ( k1_yellow_0 @ X1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D_1 @ ( k1_yellow_0 @ X1 @ X2 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('61',plain,(
    ! [X24: $i] :
      ( ( ( k3_yellow_0 @ X24 )
        = ( k1_yellow_0 @ X24 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('62',plain,(
    ! [X32: $i] :
      ( ( r1_yellow_0 @ X32 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X32 )
      | ~ ( v1_yellow_0 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('64',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X31 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('65',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( r2_hidden @ ( sk_D_1 @ X20 @ X22 @ X21 ) @ X22 )
      | ( r2_lattice3 @ X21 @ X22 @ X20 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k3_yellow_0 @ X0 ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k3_yellow_0 @ X0 ) @ X1 @ X0 ) @ X1 )
      | ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( r2_lattice3 @ X1 @ X0 @ ( k3_yellow_0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D_1 @ ( k3_yellow_0 @ X1 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    ! [X24: $i] :
      ( ( ( k3_yellow_0 @ X24 )
        = ( k1_yellow_0 @ X24 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( k3_yellow_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_yellow_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ k1_xboole_0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['62','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('86',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('87',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
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

thf('89',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v13_waybel_0 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ( r2_hidden @ X35 @ X33 )
      | ~ ( r1_orders_2 @ X34 @ X36 @ X35 )
      | ~ ( r2_hidden @ X36 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['87','93'])).

thf('95',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['80','96'])).

thf('98',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','103'])).

thf('105',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('108',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ X0 )
        | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','114'])).

thf('116',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','121'])).

thf('123',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('126',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('128',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
        | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('130',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('134',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( X6 = X4 )
      | ~ ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X4 @ X6 @ X5 ) @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('138',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['131','138'])).

thf('140',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('141',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['142'])).

thf('144',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['141','143'])).

thf('145',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('147',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ X7 @ X7 ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['142'])).

thf('150',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38 = X37 )
      | ( v1_subset_1 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('152',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('154',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X31 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_orders_2 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('156',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['154','157'])).

thf('159',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('160',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['142'])).

thf('165',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','148','149','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zjhHJHCV87
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:34:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.24/3.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.24/3.45  % Solved by: fo/fo7.sh
% 3.24/3.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.24/3.45  % done 2605 iterations in 2.986s
% 3.24/3.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.24/3.45  % SZS output start Refutation
% 3.24/3.45  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.24/3.45  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 3.24/3.45  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 3.24/3.45  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 3.24/3.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.24/3.45  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.24/3.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.24/3.45  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 3.24/3.45  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 3.24/3.45  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 3.24/3.45  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 3.24/3.45  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 3.24/3.45  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 3.24/3.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.24/3.45  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 3.24/3.45  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 3.24/3.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.24/3.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.24/3.45  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 3.24/3.45  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 3.24/3.45  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 3.24/3.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.24/3.45  thf(sk_A_type, type, sk_A: $i).
% 3.24/3.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.24/3.45  thf(sk_B_type, type, sk_B: $i > $i).
% 3.24/3.45  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 3.24/3.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.24/3.45  thf(t8_waybel_7, conjecture,
% 3.24/3.45    (![A:$i]:
% 3.24/3.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.24/3.45         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 3.24/3.45         ( l1_orders_2 @ A ) ) =>
% 3.24/3.45       ( ![B:$i]:
% 3.24/3.45         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 3.24/3.45             ( v13_waybel_0 @ B @ A ) & 
% 3.24/3.45             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.24/3.45           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 3.24/3.45             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 3.24/3.45  thf(zf_stmt_0, negated_conjecture,
% 3.24/3.45    (~( ![A:$i]:
% 3.24/3.45        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 3.24/3.45            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 3.24/3.45            ( l1_orders_2 @ A ) ) =>
% 3.24/3.45          ( ![B:$i]:
% 3.24/3.45            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 3.24/3.45                ( v13_waybel_0 @ B @ A ) & 
% 3.24/3.45                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.24/3.45              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 3.24/3.45                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 3.24/3.45    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 3.24/3.45  thf('0', plain,
% 3.24/3.45      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 3.24/3.45        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('1', plain,
% 3.24/3.45      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 3.24/3.45       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('split', [status(esa)], ['0'])).
% 3.24/3.45  thf(t42_yellow_0, axiom,
% 3.24/3.45    (![A:$i]:
% 3.24/3.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 3.24/3.45         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 3.24/3.45       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 3.24/3.45         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 3.24/3.45  thf('2', plain,
% 3.24/3.45      (![X32 : $i]:
% 3.24/3.45         ((r1_yellow_0 @ X32 @ k1_xboole_0)
% 3.24/3.45          | ~ (l1_orders_2 @ X32)
% 3.24/3.45          | ~ (v1_yellow_0 @ X32)
% 3.24/3.45          | ~ (v5_orders_2 @ X32)
% 3.24/3.45          | (v2_struct_0 @ X32))),
% 3.24/3.45      inference('cnf', [status(esa)], [t42_yellow_0])).
% 3.24/3.45  thf(t4_subset_1, axiom,
% 3.24/3.45    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.24/3.45  thf('3', plain,
% 3.24/3.45      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 3.24/3.45      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.24/3.45  thf(t3_subset, axiom,
% 3.24/3.45    (![A:$i,B:$i]:
% 3.24/3.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.24/3.45  thf('4', plain,
% 3.24/3.45      (![X12 : $i, X13 : $i]:
% 3.24/3.45         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 3.24/3.45      inference('cnf', [status(esa)], [t3_subset])).
% 3.24/3.45  thf('5', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.24/3.45      inference('sup-', [status(thm)], ['3', '4'])).
% 3.24/3.45  thf('6', plain,
% 3.24/3.45      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf(rc3_subset_1, axiom,
% 3.24/3.45    (![A:$i]:
% 3.24/3.45     ( ?[B:$i]:
% 3.24/3.45       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 3.24/3.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 3.24/3.45  thf('7', plain,
% 3.24/3.45      (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ (k1_zfmisc_1 @ X7))),
% 3.24/3.45      inference('cnf', [status(esa)], [rc3_subset_1])).
% 3.24/3.45  thf('8', plain,
% 3.24/3.45      (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ (k1_zfmisc_1 @ X7))),
% 3.24/3.45      inference('cnf', [status(esa)], [rc3_subset_1])).
% 3.24/3.45  thf(d7_subset_1, axiom,
% 3.24/3.45    (![A:$i,B:$i]:
% 3.24/3.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.24/3.45       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 3.24/3.45  thf('9', plain,
% 3.24/3.45      (![X37 : $i, X38 : $i]:
% 3.24/3.45         (((X38) = (X37))
% 3.24/3.45          | (v1_subset_1 @ X38 @ X37)
% 3.24/3.45          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 3.24/3.45      inference('cnf', [status(esa)], [d7_subset_1])).
% 3.24/3.45  thf('10', plain,
% 3.24/3.45      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['8', '9'])).
% 3.24/3.45  thf('11', plain, (![X7 : $i]: ~ (v1_subset_1 @ (sk_B @ X7) @ X7)),
% 3.24/3.45      inference('cnf', [status(esa)], [rc3_subset_1])).
% 3.24/3.45  thf('12', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 3.24/3.45      inference('clc', [status(thm)], ['10', '11'])).
% 3.24/3.45  thf('13', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 3.24/3.45      inference('demod', [status(thm)], ['7', '12'])).
% 3.24/3.45  thf(t8_subset_1, axiom,
% 3.24/3.45    (![A:$i,B:$i]:
% 3.24/3.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.24/3.45       ( ![C:$i]:
% 3.24/3.45         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.24/3.45           ( ( ![D:$i]:
% 3.24/3.45               ( ( m1_subset_1 @ D @ A ) =>
% 3.24/3.45                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 3.24/3.45             ( ( B ) = ( C ) ) ) ) ) ))).
% 3.24/3.45  thf('14', plain,
% 3.24/3.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.24/3.45         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 3.24/3.45          | ((X6) = (X4))
% 3.24/3.45          | (m1_subset_1 @ (sk_D @ X4 @ X6 @ X5) @ X5)
% 3.24/3.45          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 3.24/3.45      inference('cnf', [status(esa)], [t8_subset_1])).
% 3.24/3.45  thf('15', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 3.24/3.45          | (m1_subset_1 @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.24/3.45          | ((X1) = (X0)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['13', '14'])).
% 3.24/3.45  thf('16', plain,
% 3.24/3.45      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 3.24/3.45        | (m1_subset_1 @ 
% 3.24/3.45           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.24/3.45           (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['6', '15'])).
% 3.24/3.45  thf(d9_lattice3, axiom,
% 3.24/3.45    (![A:$i]:
% 3.24/3.45     ( ( l1_orders_2 @ A ) =>
% 3.24/3.45       ( ![B:$i,C:$i]:
% 3.24/3.45         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.24/3.45           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 3.24/3.45             ( ![D:$i]:
% 3.24/3.45               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.24/3.45                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 3.24/3.45  thf('17', plain,
% 3.24/3.45      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.24/3.45         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 3.24/3.45          | (r2_hidden @ (sk_D_1 @ X20 @ X22 @ X21) @ X22)
% 3.24/3.45          | (r2_lattice3 @ X21 @ X22 @ X20)
% 3.24/3.45          | ~ (l1_orders_2 @ X21))),
% 3.24/3.45      inference('cnf', [status(esa)], [d9_lattice3])).
% 3.24/3.45  thf('18', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 3.24/3.45          | ~ (l1_orders_2 @ sk_A)
% 3.24/3.45          | (r2_lattice3 @ sk_A @ X0 @ 
% 3.24/3.45             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.24/3.45          | (r2_hidden @ 
% 3.24/3.45             (sk_D_1 @ 
% 3.24/3.45              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.24/3.45              X0 @ sk_A) @ 
% 3.24/3.45             X0))),
% 3.24/3.45      inference('sup-', [status(thm)], ['16', '17'])).
% 3.24/3.45  thf('19', plain, ((l1_orders_2 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('20', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 3.24/3.45          | (r2_lattice3 @ sk_A @ X0 @ 
% 3.24/3.45             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.24/3.45          | (r2_hidden @ 
% 3.24/3.45             (sk_D_1 @ 
% 3.24/3.45              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.24/3.45              X0 @ sk_A) @ 
% 3.24/3.45             X0))),
% 3.24/3.45      inference('demod', [status(thm)], ['18', '19'])).
% 3.24/3.45  thf(t7_ordinal1, axiom,
% 3.24/3.45    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.24/3.45  thf('21', plain,
% 3.24/3.45      (![X18 : $i, X19 : $i]:
% 3.24/3.45         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 3.24/3.45      inference('cnf', [status(esa)], [t7_ordinal1])).
% 3.24/3.45  thf('22', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         ((r2_lattice3 @ sk_A @ X0 @ 
% 3.24/3.45           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.24/3.45          | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 3.24/3.45          | ~ (r1_tarski @ X0 @ 
% 3.24/3.45               (sk_D_1 @ 
% 3.24/3.45                (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.24/3.45                X0 @ sk_A)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['20', '21'])).
% 3.24/3.45  thf('23', plain,
% 3.24/3.45      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 3.24/3.45        | (r2_lattice3 @ sk_A @ k1_xboole_0 @ 
% 3.24/3.45           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.24/3.45      inference('sup-', [status(thm)], ['5', '22'])).
% 3.24/3.45  thf('24', plain,
% 3.24/3.45      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 3.24/3.45        | (m1_subset_1 @ 
% 3.24/3.45           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.24/3.45           (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['6', '15'])).
% 3.24/3.45  thf(dt_k1_yellow_0, axiom,
% 3.24/3.45    (![A:$i,B:$i]:
% 3.24/3.45     ( ( l1_orders_2 @ A ) =>
% 3.24/3.45       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 3.24/3.45  thf('25', plain,
% 3.24/3.45      (![X29 : $i, X30 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X29)
% 3.24/3.45          | (m1_subset_1 @ (k1_yellow_0 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 3.24/3.45      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 3.24/3.45  thf(d9_yellow_0, axiom,
% 3.24/3.45    (![A:$i]:
% 3.24/3.45     ( ( l1_orders_2 @ A ) =>
% 3.24/3.45       ( ![B:$i,C:$i]:
% 3.24/3.45         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.24/3.45           ( ( r1_yellow_0 @ A @ B ) =>
% 3.24/3.45             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 3.24/3.45               ( ( r2_lattice3 @ A @ B @ C ) & 
% 3.24/3.45                 ( ![D:$i]:
% 3.24/3.45                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.24/3.45                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 3.24/3.45                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 3.24/3.45  thf('26', plain,
% 3.24/3.45      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 3.24/3.45         (((X27) != (k1_yellow_0 @ X25 @ X26))
% 3.24/3.45          | ~ (r2_lattice3 @ X25 @ X26 @ X28)
% 3.24/3.45          | (r1_orders_2 @ X25 @ X27 @ X28)
% 3.24/3.45          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X25))
% 3.24/3.45          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 3.24/3.45          | ~ (r1_yellow_0 @ X25 @ X26)
% 3.24/3.45          | ~ (l1_orders_2 @ X25))),
% 3.24/3.45      inference('cnf', [status(esa)], [d9_yellow_0])).
% 3.24/3.45  thf('27', plain,
% 3.24/3.45      (![X25 : $i, X26 : $i, X28 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X25)
% 3.24/3.45          | ~ (r1_yellow_0 @ X25 @ X26)
% 3.24/3.45          | ~ (m1_subset_1 @ (k1_yellow_0 @ X25 @ X26) @ (u1_struct_0 @ X25))
% 3.24/3.45          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X25))
% 3.24/3.45          | (r1_orders_2 @ X25 @ (k1_yellow_0 @ X25 @ X26) @ X28)
% 3.24/3.45          | ~ (r2_lattice3 @ X25 @ X26 @ X28))),
% 3.24/3.45      inference('simplify', [status(thm)], ['26'])).
% 3.24/3.45  thf('28', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X0)
% 3.24/3.45          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 3.24/3.45          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 3.24/3.45          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 3.24/3.45          | ~ (r1_yellow_0 @ X0 @ X1)
% 3.24/3.45          | ~ (l1_orders_2 @ X0))),
% 3.24/3.45      inference('sup-', [status(thm)], ['25', '27'])).
% 3.24/3.45  thf('29', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.24/3.45         (~ (r1_yellow_0 @ X0 @ X1)
% 3.24/3.45          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 3.24/3.45          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 3.24/3.45          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 3.24/3.45          | ~ (l1_orders_2 @ X0))),
% 3.24/3.45      inference('simplify', [status(thm)], ['28'])).
% 3.24/3.45  thf('30', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 3.24/3.45          | ~ (l1_orders_2 @ sk_A)
% 3.24/3.45          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 3.24/3.45               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.24/3.45          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 3.24/3.45             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.24/3.45          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 3.24/3.45      inference('sup-', [status(thm)], ['24', '29'])).
% 3.24/3.45  thf('31', plain, ((l1_orders_2 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('32', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 3.24/3.45          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 3.24/3.45               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.24/3.45          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 3.24/3.45             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.24/3.45          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 3.24/3.45      inference('demod', [status(thm)], ['30', '31'])).
% 3.24/3.45  thf('33', plain,
% 3.24/3.45      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 3.24/3.45        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 3.24/3.45        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.24/3.45           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.24/3.45        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['23', '32'])).
% 3.24/3.45  thf('34', plain,
% 3.24/3.45      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.24/3.45         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.24/3.45        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 3.24/3.45        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('simplify', [status(thm)], ['33'])).
% 3.24/3.45  thf('35', plain,
% 3.24/3.45      (((v2_struct_0 @ sk_A)
% 3.24/3.45        | ~ (v5_orders_2 @ sk_A)
% 3.24/3.45        | ~ (v1_yellow_0 @ sk_A)
% 3.24/3.45        | ~ (l1_orders_2 @ sk_A)
% 3.24/3.45        | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 3.24/3.45        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.24/3.45           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.24/3.45      inference('sup-', [status(thm)], ['2', '34'])).
% 3.24/3.45  thf('36', plain, ((v5_orders_2 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('37', plain, ((v1_yellow_0 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('38', plain, ((l1_orders_2 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('39', plain,
% 3.24/3.45      (((v2_struct_0 @ sk_A)
% 3.24/3.45        | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 3.24/3.45        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.24/3.45           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.24/3.45      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 3.24/3.45  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('41', plain,
% 3.24/3.45      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.24/3.45         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.24/3.45        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('clc', [status(thm)], ['39', '40'])).
% 3.24/3.45  thf('42', plain,
% 3.24/3.45      (![X29 : $i, X30 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X29)
% 3.24/3.45          | (m1_subset_1 @ (k1_yellow_0 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 3.24/3.45      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 3.24/3.45  thf('43', plain,
% 3.24/3.45      (![X32 : $i]:
% 3.24/3.45         ((r1_yellow_0 @ X32 @ k1_xboole_0)
% 3.24/3.45          | ~ (l1_orders_2 @ X32)
% 3.24/3.45          | ~ (v1_yellow_0 @ X32)
% 3.24/3.45          | ~ (v5_orders_2 @ X32)
% 3.24/3.45          | (v2_struct_0 @ X32))),
% 3.24/3.45      inference('cnf', [status(esa)], [t42_yellow_0])).
% 3.24/3.45  thf('44', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.24/3.45      inference('sup-', [status(thm)], ['3', '4'])).
% 3.24/3.45  thf('45', plain,
% 3.24/3.45      (![X29 : $i, X30 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X29)
% 3.24/3.45          | (m1_subset_1 @ (k1_yellow_0 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 3.24/3.45      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 3.24/3.45  thf('46', plain,
% 3.24/3.45      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.24/3.45         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 3.24/3.45          | (r2_hidden @ (sk_D_1 @ X20 @ X22 @ X21) @ X22)
% 3.24/3.45          | (r2_lattice3 @ X21 @ X22 @ X20)
% 3.24/3.45          | ~ (l1_orders_2 @ X21))),
% 3.24/3.45      inference('cnf', [status(esa)], [d9_lattice3])).
% 3.24/3.45  thf('47', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X0)
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 3.24/3.45          | (r2_hidden @ (sk_D_1 @ (k1_yellow_0 @ X0 @ X1) @ X2 @ X0) @ X2))),
% 3.24/3.45      inference('sup-', [status(thm)], ['45', '46'])).
% 3.24/3.45  thf('48', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.24/3.45         ((r2_hidden @ (sk_D_1 @ (k1_yellow_0 @ X0 @ X1) @ X2 @ X0) @ X2)
% 3.24/3.45          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 3.24/3.45          | ~ (l1_orders_2 @ X0))),
% 3.24/3.45      inference('simplify', [status(thm)], ['47'])).
% 3.24/3.45  thf('49', plain,
% 3.24/3.45      (![X18 : $i, X19 : $i]:
% 3.24/3.45         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 3.24/3.45      inference('cnf', [status(esa)], [t7_ordinal1])).
% 3.24/3.45  thf('50', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X1)
% 3.24/3.45          | (r2_lattice3 @ X1 @ X0 @ (k1_yellow_0 @ X1 @ X2))
% 3.24/3.45          | ~ (r1_tarski @ X0 @ (sk_D_1 @ (k1_yellow_0 @ X1 @ X2) @ X0 @ X1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['48', '49'])).
% 3.24/3.45  thf('51', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         ((r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ X1))
% 3.24/3.45          | ~ (l1_orders_2 @ X0))),
% 3.24/3.45      inference('sup-', [status(thm)], ['44', '50'])).
% 3.24/3.45  thf('52', plain,
% 3.24/3.45      (![X29 : $i, X30 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X29)
% 3.24/3.45          | (m1_subset_1 @ (k1_yellow_0 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 3.24/3.45      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 3.24/3.45  thf('53', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.24/3.45         (~ (r1_yellow_0 @ X0 @ X1)
% 3.24/3.45          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 3.24/3.45          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 3.24/3.45          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 3.24/3.45          | ~ (l1_orders_2 @ X0))),
% 3.24/3.45      inference('simplify', [status(thm)], ['28'])).
% 3.24/3.45  thf('54', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X0)
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 3.24/3.45          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 3.24/3.45             (k1_yellow_0 @ X0 @ X1))
% 3.24/3.45          | ~ (r1_yellow_0 @ X0 @ X2))),
% 3.24/3.45      inference('sup-', [status(thm)], ['52', '53'])).
% 3.24/3.45  thf('55', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.24/3.45         (~ (r1_yellow_0 @ X0 @ X2)
% 3.24/3.45          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 3.24/3.45             (k1_yellow_0 @ X0 @ X1))
% 3.24/3.45          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 3.24/3.45          | ~ (l1_orders_2 @ X0))),
% 3.24/3.45      inference('simplify', [status(thm)], ['54'])).
% 3.24/3.45  thf('56', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X1)
% 3.24/3.45          | ~ (l1_orders_2 @ X1)
% 3.24/3.45          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 3.24/3.45             (k1_yellow_0 @ X1 @ X0))
% 3.24/3.45          | ~ (r1_yellow_0 @ X1 @ k1_xboole_0))),
% 3.24/3.45      inference('sup-', [status(thm)], ['51', '55'])).
% 3.24/3.45  thf('57', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         (~ (r1_yellow_0 @ X1 @ k1_xboole_0)
% 3.24/3.45          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 3.24/3.45             (k1_yellow_0 @ X1 @ X0))
% 3.24/3.45          | ~ (l1_orders_2 @ X1))),
% 3.24/3.45      inference('simplify', [status(thm)], ['56'])).
% 3.24/3.45  thf('58', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         ((v2_struct_0 @ X0)
% 3.24/3.45          | ~ (v5_orders_2 @ X0)
% 3.24/3.45          | ~ (v1_yellow_0 @ X0)
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 3.24/3.45             (k1_yellow_0 @ X0 @ X1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['43', '57'])).
% 3.24/3.45  thf('59', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 3.24/3.45           (k1_yellow_0 @ X0 @ X1))
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | ~ (v1_yellow_0 @ X0)
% 3.24/3.45          | ~ (v5_orders_2 @ X0)
% 3.24/3.45          | (v2_struct_0 @ X0))),
% 3.24/3.45      inference('simplify', [status(thm)], ['58'])).
% 3.24/3.45  thf('60', plain,
% 3.24/3.45      (![X29 : $i, X30 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X29)
% 3.24/3.45          | (m1_subset_1 @ (k1_yellow_0 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 3.24/3.45      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 3.24/3.45  thf(d11_yellow_0, axiom,
% 3.24/3.45    (![A:$i]:
% 3.24/3.45     ( ( l1_orders_2 @ A ) =>
% 3.24/3.45       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 3.24/3.45  thf('61', plain,
% 3.24/3.45      (![X24 : $i]:
% 3.24/3.45         (((k3_yellow_0 @ X24) = (k1_yellow_0 @ X24 @ k1_xboole_0))
% 3.24/3.45          | ~ (l1_orders_2 @ X24))),
% 3.24/3.45      inference('cnf', [status(esa)], [d11_yellow_0])).
% 3.24/3.45  thf('62', plain,
% 3.24/3.45      (![X32 : $i]:
% 3.24/3.45         ((r1_yellow_0 @ X32 @ k1_xboole_0)
% 3.24/3.45          | ~ (l1_orders_2 @ X32)
% 3.24/3.45          | ~ (v1_yellow_0 @ X32)
% 3.24/3.45          | ~ (v5_orders_2 @ X32)
% 3.24/3.45          | (v2_struct_0 @ X32))),
% 3.24/3.45      inference('cnf', [status(esa)], [t42_yellow_0])).
% 3.24/3.45  thf('63', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.24/3.45      inference('sup-', [status(thm)], ['3', '4'])).
% 3.24/3.45  thf(dt_k3_yellow_0, axiom,
% 3.24/3.45    (![A:$i]:
% 3.24/3.45     ( ( l1_orders_2 @ A ) =>
% 3.24/3.45       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 3.24/3.45  thf('64', plain,
% 3.24/3.45      (![X31 : $i]:
% 3.24/3.45         ((m1_subset_1 @ (k3_yellow_0 @ X31) @ (u1_struct_0 @ X31))
% 3.24/3.45          | ~ (l1_orders_2 @ X31))),
% 3.24/3.45      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 3.24/3.45  thf('65', plain,
% 3.24/3.45      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.24/3.45         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 3.24/3.45          | (r2_hidden @ (sk_D_1 @ X20 @ X22 @ X21) @ X22)
% 3.24/3.45          | (r2_lattice3 @ X21 @ X22 @ X20)
% 3.24/3.45          | ~ (l1_orders_2 @ X21))),
% 3.24/3.45      inference('cnf', [status(esa)], [d9_lattice3])).
% 3.24/3.45  thf('66', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X0)
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 3.24/3.45          | (r2_hidden @ (sk_D_1 @ (k3_yellow_0 @ X0) @ X1 @ X0) @ X1))),
% 3.24/3.45      inference('sup-', [status(thm)], ['64', '65'])).
% 3.24/3.45  thf('67', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         ((r2_hidden @ (sk_D_1 @ (k3_yellow_0 @ X0) @ X1 @ X0) @ X1)
% 3.24/3.45          | (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 3.24/3.45          | ~ (l1_orders_2 @ X0))),
% 3.24/3.45      inference('simplify', [status(thm)], ['66'])).
% 3.24/3.45  thf('68', plain,
% 3.24/3.45      (![X18 : $i, X19 : $i]:
% 3.24/3.45         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 3.24/3.45      inference('cnf', [status(esa)], [t7_ordinal1])).
% 3.24/3.45  thf('69', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X1)
% 3.24/3.45          | (r2_lattice3 @ X1 @ X0 @ (k3_yellow_0 @ X1))
% 3.24/3.45          | ~ (r1_tarski @ X0 @ (sk_D_1 @ (k3_yellow_0 @ X1) @ X0 @ X1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['67', '68'])).
% 3.24/3.45  thf('70', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         ((r2_lattice3 @ X0 @ k1_xboole_0 @ (k3_yellow_0 @ X0))
% 3.24/3.45          | ~ (l1_orders_2 @ X0))),
% 3.24/3.45      inference('sup-', [status(thm)], ['63', '69'])).
% 3.24/3.45  thf('71', plain,
% 3.24/3.45      (![X24 : $i]:
% 3.24/3.45         (((k3_yellow_0 @ X24) = (k1_yellow_0 @ X24 @ k1_xboole_0))
% 3.24/3.45          | ~ (l1_orders_2 @ X24))),
% 3.24/3.45      inference('cnf', [status(esa)], [d11_yellow_0])).
% 3.24/3.45  thf('72', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.24/3.45         (~ (r1_yellow_0 @ X0 @ X2)
% 3.24/3.45          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 3.24/3.45             (k1_yellow_0 @ X0 @ X1))
% 3.24/3.45          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 3.24/3.45          | ~ (l1_orders_2 @ X0))),
% 3.24/3.45      inference('simplify', [status(thm)], ['54'])).
% 3.24/3.45  thf('73', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         (~ (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0))
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 3.24/3.45             (k1_yellow_0 @ X0 @ k1_xboole_0))
% 3.24/3.45          | ~ (r1_yellow_0 @ X0 @ X1))),
% 3.24/3.45      inference('sup-', [status(thm)], ['71', '72'])).
% 3.24/3.45  thf('74', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         (~ (r1_yellow_0 @ X0 @ X1)
% 3.24/3.45          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 3.24/3.45             (k1_yellow_0 @ X0 @ k1_xboole_0))
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | ~ (r2_lattice3 @ X0 @ X1 @ (k3_yellow_0 @ X0)))),
% 3.24/3.45      inference('simplify', [status(thm)], ['73'])).
% 3.24/3.45  thf('75', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X0)
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 3.24/3.45             (k1_yellow_0 @ X0 @ k1_xboole_0))
% 3.24/3.45          | ~ (r1_yellow_0 @ X0 @ k1_xboole_0))),
% 3.24/3.45      inference('sup-', [status(thm)], ['70', '74'])).
% 3.24/3.45  thf('76', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         (~ (r1_yellow_0 @ X0 @ k1_xboole_0)
% 3.24/3.45          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 3.24/3.45             (k1_yellow_0 @ X0 @ k1_xboole_0))
% 3.24/3.45          | ~ (l1_orders_2 @ X0))),
% 3.24/3.45      inference('simplify', [status(thm)], ['75'])).
% 3.24/3.45  thf('77', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         ((v2_struct_0 @ X0)
% 3.24/3.45          | ~ (v5_orders_2 @ X0)
% 3.24/3.45          | ~ (v1_yellow_0 @ X0)
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 3.24/3.45             (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['62', '76'])).
% 3.24/3.45  thf('78', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 3.24/3.45           (k1_yellow_0 @ X0 @ k1_xboole_0))
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | ~ (v1_yellow_0 @ X0)
% 3.24/3.45          | ~ (v5_orders_2 @ X0)
% 3.24/3.45          | (v2_struct_0 @ X0))),
% 3.24/3.45      inference('simplify', [status(thm)], ['77'])).
% 3.24/3.45  thf('79', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 3.24/3.45           (k1_yellow_0 @ X0 @ k1_xboole_0))
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | (v2_struct_0 @ X0)
% 3.24/3.45          | ~ (v5_orders_2 @ X0)
% 3.24/3.45          | ~ (v1_yellow_0 @ X0)
% 3.24/3.45          | ~ (l1_orders_2 @ X0))),
% 3.24/3.45      inference('sup+', [status(thm)], ['61', '78'])).
% 3.24/3.45  thf('80', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         (~ (v1_yellow_0 @ X0)
% 3.24/3.45          | ~ (v5_orders_2 @ X0)
% 3.24/3.45          | (v2_struct_0 @ X0)
% 3.24/3.45          | ~ (l1_orders_2 @ X0)
% 3.24/3.45          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 3.24/3.45             (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 3.24/3.45      inference('simplify', [status(thm)], ['79'])).
% 3.24/3.45  thf('81', plain,
% 3.24/3.45      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('split', [status(esa)], ['0'])).
% 3.24/3.45  thf('82', plain,
% 3.24/3.45      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf(l3_subset_1, axiom,
% 3.24/3.45    (![A:$i,B:$i]:
% 3.24/3.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.24/3.45       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 3.24/3.45  thf('83', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.24/3.45         (~ (r2_hidden @ X0 @ X1)
% 3.24/3.45          | (r2_hidden @ X0 @ X2)
% 3.24/3.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 3.24/3.45      inference('cnf', [status(esa)], [l3_subset_1])).
% 3.24/3.45  thf('84', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 3.24/3.45      inference('sup-', [status(thm)], ['82', '83'])).
% 3.24/3.45  thf('85', plain,
% 3.24/3.45      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['81', '84'])).
% 3.24/3.45  thf(t1_subset, axiom,
% 3.24/3.45    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 3.24/3.45  thf('86', plain,
% 3.24/3.45      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 3.24/3.45      inference('cnf', [status(esa)], [t1_subset])).
% 3.24/3.45  thf('87', plain,
% 3.24/3.45      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['85', '86'])).
% 3.24/3.45  thf('88', plain,
% 3.24/3.45      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf(d20_waybel_0, axiom,
% 3.24/3.45    (![A:$i]:
% 3.24/3.45     ( ( l1_orders_2 @ A ) =>
% 3.24/3.45       ( ![B:$i]:
% 3.24/3.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.24/3.45           ( ( v13_waybel_0 @ B @ A ) <=>
% 3.24/3.45             ( ![C:$i]:
% 3.24/3.45               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.24/3.45                 ( ![D:$i]:
% 3.24/3.45                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.24/3.45                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 3.24/3.45                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 3.24/3.45  thf('89', plain,
% 3.24/3.45      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.24/3.45         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 3.24/3.45          | ~ (v13_waybel_0 @ X33 @ X34)
% 3.24/3.45          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X34))
% 3.24/3.45          | (r2_hidden @ X35 @ X33)
% 3.24/3.45          | ~ (r1_orders_2 @ X34 @ X36 @ X35)
% 3.24/3.45          | ~ (r2_hidden @ X36 @ X33)
% 3.24/3.45          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X34))
% 3.24/3.45          | ~ (l1_orders_2 @ X34))),
% 3.24/3.45      inference('cnf', [status(esa)], [d20_waybel_0])).
% 3.24/3.45  thf('90', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ sk_A)
% 3.24/3.45          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.24/3.45          | ~ (r2_hidden @ X0 @ sk_B_1)
% 3.24/3.45          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 3.24/3.45          | (r2_hidden @ X1 @ sk_B_1)
% 3.24/3.45          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.24/3.45          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 3.24/3.45      inference('sup-', [status(thm)], ['88', '89'])).
% 3.24/3.45  thf('91', plain, ((l1_orders_2 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('92', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('93', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.24/3.45          | ~ (r2_hidden @ X0 @ sk_B_1)
% 3.24/3.45          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 3.24/3.45          | (r2_hidden @ X1 @ sk_B_1)
% 3.24/3.45          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('demod', [status(thm)], ['90', '91', '92'])).
% 3.24/3.45  thf('94', plain,
% 3.24/3.45      ((![X0 : $i]:
% 3.24/3.45          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.24/3.45           | (r2_hidden @ X0 @ sk_B_1)
% 3.24/3.45           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 3.24/3.45           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['87', '93'])).
% 3.24/3.45  thf('95', plain,
% 3.24/3.45      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('split', [status(esa)], ['0'])).
% 3.24/3.45  thf('96', plain,
% 3.24/3.45      ((![X0 : $i]:
% 3.24/3.45          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.24/3.45           | (r2_hidden @ X0 @ sk_B_1)
% 3.24/3.45           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('demod', [status(thm)], ['94', '95'])).
% 3.24/3.45  thf('97', plain,
% 3.24/3.45      (((~ (l1_orders_2 @ sk_A)
% 3.24/3.45         | (v2_struct_0 @ sk_A)
% 3.24/3.45         | ~ (v5_orders_2 @ sk_A)
% 3.24/3.45         | ~ (v1_yellow_0 @ sk_A)
% 3.24/3.45         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ sk_B_1)
% 3.24/3.45         | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.24/3.45              (u1_struct_0 @ sk_A))))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['80', '96'])).
% 3.24/3.45  thf('98', plain, ((l1_orders_2 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('99', plain, ((v5_orders_2 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('100', plain, ((v1_yellow_0 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('101', plain,
% 3.24/3.45      ((((v2_struct_0 @ sk_A)
% 3.24/3.45         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ sk_B_1)
% 3.24/3.45         | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.24/3.45              (u1_struct_0 @ sk_A))))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 3.24/3.45  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('103', plain,
% 3.24/3.45      (((~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.24/3.45            (u1_struct_0 @ sk_A))
% 3.24/3.45         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ sk_B_1)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('clc', [status(thm)], ['101', '102'])).
% 3.24/3.45  thf('104', plain,
% 3.24/3.45      (((~ (l1_orders_2 @ sk_A)
% 3.24/3.45         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ sk_B_1)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['60', '103'])).
% 3.24/3.45  thf('105', plain, ((l1_orders_2 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('106', plain,
% 3.24/3.45      (((r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ sk_B_1))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('demod', [status(thm)], ['104', '105'])).
% 3.24/3.45  thf('107', plain,
% 3.24/3.45      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf(t4_subset, axiom,
% 3.24/3.45    (![A:$i,B:$i,C:$i]:
% 3.24/3.45     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 3.24/3.45       ( m1_subset_1 @ A @ C ) ))).
% 3.24/3.45  thf('108', plain,
% 3.24/3.45      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.24/3.45         (~ (r2_hidden @ X15 @ X16)
% 3.24/3.45          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 3.24/3.45          | (m1_subset_1 @ X15 @ X17))),
% 3.24/3.45      inference('cnf', [status(esa)], [t4_subset])).
% 3.24/3.45  thf('109', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.24/3.45          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 3.24/3.45      inference('sup-', [status(thm)], ['107', '108'])).
% 3.24/3.45  thf('110', plain,
% 3.24/3.45      (((m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 3.24/3.45         (u1_struct_0 @ sk_A)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['106', '109'])).
% 3.24/3.45  thf('111', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.24/3.45          | ~ (r2_hidden @ X0 @ sk_B_1)
% 3.24/3.45          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 3.24/3.45          | (r2_hidden @ X1 @ sk_B_1)
% 3.24/3.45          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('demod', [status(thm)], ['90', '91', '92'])).
% 3.24/3.45  thf('112', plain,
% 3.24/3.45      ((![X0 : $i]:
% 3.24/3.45          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.24/3.45           | (r2_hidden @ X0 @ sk_B_1)
% 3.24/3.45           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ X0)
% 3.24/3.45           | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ sk_B_1)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['110', '111'])).
% 3.24/3.45  thf('113', plain,
% 3.24/3.45      (((r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ sk_B_1))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('demod', [status(thm)], ['104', '105'])).
% 3.24/3.45  thf('114', plain,
% 3.24/3.45      ((![X0 : $i]:
% 3.24/3.45          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.24/3.45           | (r2_hidden @ X0 @ sk_B_1)
% 3.24/3.45           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ X0)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('demod', [status(thm)], ['112', '113'])).
% 3.24/3.45  thf('115', plain,
% 3.24/3.45      ((![X0 : $i]:
% 3.24/3.45          ((v2_struct_0 @ sk_A)
% 3.24/3.45           | ~ (v5_orders_2 @ sk_A)
% 3.24/3.45           | ~ (v1_yellow_0 @ sk_A)
% 3.24/3.45           | ~ (l1_orders_2 @ sk_A)
% 3.24/3.45           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 3.24/3.45           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['59', '114'])).
% 3.24/3.45  thf('116', plain, ((v5_orders_2 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('117', plain, ((v1_yellow_0 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('118', plain, ((l1_orders_2 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('119', plain,
% 3.24/3.45      ((![X0 : $i]:
% 3.24/3.45          ((v2_struct_0 @ sk_A)
% 3.24/3.45           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 3.24/3.45           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 3.24/3.45  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('121', plain,
% 3.24/3.45      ((![X0 : $i]:
% 3.24/3.45          (~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 3.24/3.45           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('clc', [status(thm)], ['119', '120'])).
% 3.24/3.45  thf('122', plain,
% 3.24/3.45      ((![X0 : $i]:
% 3.24/3.45          (~ (l1_orders_2 @ sk_A)
% 3.24/3.45           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['42', '121'])).
% 3.24/3.45  thf('123', plain, ((l1_orders_2 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('124', plain,
% 3.24/3.45      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('demod', [status(thm)], ['122', '123'])).
% 3.24/3.45  thf('125', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.24/3.45          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 3.24/3.45      inference('sup-', [status(thm)], ['107', '108'])).
% 3.24/3.45  thf('126', plain,
% 3.24/3.45      ((![X0 : $i]:
% 3.24/3.45          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['124', '125'])).
% 3.24/3.45  thf('127', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 3.24/3.45          | ~ (r2_hidden @ X0 @ sk_B_1)
% 3.24/3.45          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 3.24/3.45          | (r2_hidden @ X1 @ sk_B_1)
% 3.24/3.45          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('demod', [status(thm)], ['90', '91', '92'])).
% 3.24/3.45  thf('128', plain,
% 3.24/3.45      ((![X0 : $i, X1 : $i]:
% 3.24/3.45          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.24/3.45           | (r2_hidden @ X1 @ sk_B_1)
% 3.24/3.45           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 3.24/3.45           | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['126', '127'])).
% 3.24/3.45  thf('129', plain,
% 3.24/3.45      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('demod', [status(thm)], ['122', '123'])).
% 3.24/3.45  thf('130', plain,
% 3.24/3.45      ((![X0 : $i, X1 : $i]:
% 3.24/3.45          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 3.24/3.45           | (r2_hidden @ X1 @ sk_B_1)
% 3.24/3.45           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('demod', [status(thm)], ['128', '129'])).
% 3.24/3.45  thf('131', plain,
% 3.24/3.45      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 3.24/3.45         | (r2_hidden @ 
% 3.24/3.45            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.24/3.45            sk_B_1)
% 3.24/3.45         | ~ (m1_subset_1 @ 
% 3.24/3.45              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.24/3.45              (u1_struct_0 @ sk_A))))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['41', '130'])).
% 3.24/3.45  thf('132', plain,
% 3.24/3.45      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('133', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 3.24/3.45      inference('demod', [status(thm)], ['7', '12'])).
% 3.24/3.45  thf('134', plain,
% 3.24/3.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.24/3.45         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 3.24/3.45          | ((X6) = (X4))
% 3.24/3.45          | ~ (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X6)
% 3.24/3.45          | ~ (r2_hidden @ (sk_D @ X4 @ X6 @ X5) @ X4)
% 3.24/3.45          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 3.24/3.45      inference('cnf', [status(esa)], [t8_subset_1])).
% 3.24/3.45  thf('135', plain,
% 3.24/3.45      (![X0 : $i, X1 : $i]:
% 3.24/3.45         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 3.24/3.45          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.24/3.45          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 3.24/3.45          | ((X1) = (X0)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['133', '134'])).
% 3.24/3.45  thf('136', plain,
% 3.24/3.45      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 3.24/3.45        | ~ (r2_hidden @ 
% 3.24/3.45             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.24/3.45             sk_B_1)
% 3.24/3.45        | ~ (r2_hidden @ 
% 3.24/3.45             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.24/3.45             (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['132', '135'])).
% 3.24/3.45  thf('137', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 3.24/3.45      inference('sup-', [status(thm)], ['82', '83'])).
% 3.24/3.45  thf('138', plain,
% 3.24/3.45      ((~ (r2_hidden @ 
% 3.24/3.45           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.24/3.45           sk_B_1)
% 3.24/3.45        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('clc', [status(thm)], ['136', '137'])).
% 3.24/3.45  thf('139', plain,
% 3.24/3.45      (((~ (m1_subset_1 @ 
% 3.24/3.45            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.24/3.45            (u1_struct_0 @ sk_A))
% 3.24/3.45         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('clc', [status(thm)], ['131', '138'])).
% 3.24/3.45  thf('140', plain,
% 3.24/3.45      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 3.24/3.45        | (m1_subset_1 @ 
% 3.24/3.45           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 3.24/3.45           (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['6', '15'])).
% 3.24/3.45  thf('141', plain,
% 3.24/3.45      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 3.24/3.45         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('clc', [status(thm)], ['139', '140'])).
% 3.24/3.45  thf('142', plain,
% 3.24/3.45      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 3.24/3.45        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('143', plain,
% 3.24/3.45      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.24/3.45         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.24/3.45      inference('split', [status(esa)], ['142'])).
% 3.24/3.45  thf('144', plain,
% 3.24/3.45      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 3.24/3.45         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 3.24/3.45             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('sup+', [status(thm)], ['141', '143'])).
% 3.24/3.45  thf('145', plain, (![X7 : $i]: ~ (v1_subset_1 @ (sk_B @ X7) @ X7)),
% 3.24/3.45      inference('cnf', [status(esa)], [rc3_subset_1])).
% 3.24/3.45  thf('146', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 3.24/3.45      inference('clc', [status(thm)], ['10', '11'])).
% 3.24/3.45  thf('147', plain, (![X7 : $i]: ~ (v1_subset_1 @ X7 @ X7)),
% 3.24/3.45      inference('demod', [status(thm)], ['145', '146'])).
% 3.24/3.45  thf('148', plain,
% 3.24/3.45      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 3.24/3.45       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['144', '147'])).
% 3.24/3.45  thf('149', plain,
% 3.24/3.45      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 3.24/3.45       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('split', [status(esa)], ['142'])).
% 3.24/3.45  thf('150', plain,
% 3.24/3.45      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('151', plain,
% 3.24/3.45      (![X37 : $i, X38 : $i]:
% 3.24/3.45         (((X38) = (X37))
% 3.24/3.45          | (v1_subset_1 @ X38 @ X37)
% 3.24/3.45          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 3.24/3.45      inference('cnf', [status(esa)], [d7_subset_1])).
% 3.24/3.45  thf('152', plain,
% 3.24/3.45      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 3.24/3.45        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['150', '151'])).
% 3.24/3.45  thf('153', plain,
% 3.24/3.45      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 3.24/3.45         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.24/3.45      inference('split', [status(esa)], ['0'])).
% 3.24/3.45  thf('154', plain,
% 3.24/3.45      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 3.24/3.45         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.24/3.45      inference('sup-', [status(thm)], ['152', '153'])).
% 3.24/3.45  thf('155', plain,
% 3.24/3.45      (![X31 : $i]:
% 3.24/3.45         ((m1_subset_1 @ (k3_yellow_0 @ X31) @ (u1_struct_0 @ X31))
% 3.24/3.45          | ~ (l1_orders_2 @ X31))),
% 3.24/3.45      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 3.24/3.45  thf(t2_subset, axiom,
% 3.24/3.45    (![A:$i,B:$i]:
% 3.24/3.45     ( ( m1_subset_1 @ A @ B ) =>
% 3.24/3.45       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 3.24/3.45  thf('156', plain,
% 3.24/3.45      (![X10 : $i, X11 : $i]:
% 3.24/3.45         ((r2_hidden @ X10 @ X11)
% 3.24/3.45          | (v1_xboole_0 @ X11)
% 3.24/3.45          | ~ (m1_subset_1 @ X10 @ X11))),
% 3.24/3.45      inference('cnf', [status(esa)], [t2_subset])).
% 3.24/3.45  thf('157', plain,
% 3.24/3.45      (![X0 : $i]:
% 3.24/3.45         (~ (l1_orders_2 @ X0)
% 3.24/3.45          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 3.24/3.45          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['155', '156'])).
% 3.24/3.45  thf('158', plain,
% 3.24/3.45      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 3.24/3.45         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.24/3.45         | ~ (l1_orders_2 @ sk_A)))
% 3.24/3.45         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.24/3.45      inference('sup+', [status(thm)], ['154', '157'])).
% 3.24/3.45  thf('159', plain,
% 3.24/3.45      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 3.24/3.45         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.24/3.45      inference('sup-', [status(thm)], ['152', '153'])).
% 3.24/3.45  thf('160', plain, ((l1_orders_2 @ sk_A)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('161', plain,
% 3.24/3.45      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1) | (v1_xboole_0 @ sk_B_1)))
% 3.24/3.45         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.24/3.45      inference('demod', [status(thm)], ['158', '159', '160'])).
% 3.24/3.45  thf('162', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 3.24/3.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.24/3.45  thf('163', plain,
% 3.24/3.45      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 3.24/3.45         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 3.24/3.45      inference('clc', [status(thm)], ['161', '162'])).
% 3.24/3.45  thf('164', plain,
% 3.24/3.45      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 3.24/3.45         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 3.24/3.45      inference('split', [status(esa)], ['142'])).
% 3.24/3.45  thf('165', plain,
% 3.24/3.45      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 3.24/3.45       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 3.24/3.45      inference('sup-', [status(thm)], ['163', '164'])).
% 3.24/3.45  thf('166', plain, ($false),
% 3.24/3.45      inference('sat_resolution*', [status(thm)], ['1', '148', '149', '165'])).
% 3.24/3.45  
% 3.24/3.45  % SZS output end Refutation
% 3.24/3.45  
% 3.24/3.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
