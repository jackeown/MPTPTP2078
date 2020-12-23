%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gu9XS5qhKb

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:12 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  252 ( 448 expanded)
%              Number of leaves         :   48 ( 150 expanded)
%              Depth                    :   40
%              Number of atoms          : 2363 (6992 expanded)
%              Number of equality atoms :   42 (  64 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X7 @ X8 ) @ X8 )
      | ( X8 = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('4',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ( ( k1_yellow_0 @ X31 @ ( k5_waybel_0 @ X31 @ X30 ) )
        = X30 )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v5_orders_2 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('6',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
      = sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B_1 ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('16',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ( ( k1_yellow_0 @ X31 @ ( k5_waybel_0 @ X31 @ X30 ) )
        = X30 )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v5_orders_2 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k1_yellow_0 @ X0 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) )
        = ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_yellow_0 @ X0 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X18: $i] :
      ( ( ( k3_yellow_0 @ X18 )
        = ( k1_yellow_0 @ X18 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('21',plain,(
    ! [X18: $i] :
      ( ( ( k3_yellow_0 @ X18 )
        = ( k1_yellow_0 @ X18 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf(t42_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( r1_yellow_0 @ A @ k1_xboole_0 )
        & ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X25: $i] :
      ( ( r1_yellow_0 @ X25 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v1_yellow_0 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X25: $i] :
      ( ( r1_yellow_0 @ X25 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v1_yellow_0 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf(t34_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( ( r1_tarski @ B @ C )
            & ( r1_yellow_0 @ A @ B )
            & ( r1_yellow_0 @ A @ C ) )
         => ( r1_orders_2 @ A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_orders_2 @ X22 @ ( k1_yellow_0 @ X22 @ X23 ) @ ( k1_yellow_0 @ X22 @ X24 ) )
      | ~ ( r1_yellow_0 @ X22 @ X24 )
      | ~ ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_yellow_0 @ X22 @ X23 )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t34_yellow_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ k1_xboole_0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
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
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('37',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('38',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X26 @ X27 ) @ X26 )
      | ( v13_waybel_0 @ X26 @ X27 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('42',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('46',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X26 @ X27 ) @ ( u1_struct_0 @ X27 ) )
      | ( v13_waybel_0 @ X26 @ X27 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X26 @ X27 ) @ X26 )
      | ( v13_waybel_0 @ X26 @ X27 )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['44','54'])).

thf('56',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('58',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('62',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v13_waybel_0 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ( r2_hidden @ X28 @ X26 )
      | ~ ( r1_orders_2 @ X27 @ X29 @ X28 )
      | ~ ( r2_hidden @ X29 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ X0 @ X1 @ X2 )
      | ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v13_waybel_0 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( v13_waybel_0 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['75','78'])).

thf('80',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','79'])).

thf('81',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ~ ( v13_waybel_0 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['64','80','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','82'])).

thf('84',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','85'])).

thf('87',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','92'])).

thf('94',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('97',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ( ( k1_yellow_0 @ X31 @ ( k5_waybel_0 @ X31 @ X30 ) )
        = X30 )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v5_orders_2 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('101',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
        = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
        = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) ) )
      = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k3_yellow_0 @ sk_A ) ) )
        = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['19','108'])).

thf('110',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('111',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ( ( k1_yellow_0 @ X31 @ ( k5_waybel_0 @ X31 @ X30 ) )
        = X30 )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v5_orders_2 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('112',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k3_yellow_0 @ sk_A ) ) )
        = ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k3_yellow_0 @ sk_A ) ) )
        = ( k3_yellow_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k3_yellow_0 @ sk_A ) ) )
      = ( k3_yellow_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( k3_yellow_0 @ sk_A )
      = ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['109','119','120'])).

thf('122',plain,(
    ! [X25: $i] :
      ( ( r1_yellow_0 @ X25 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v1_yellow_0 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('123',plain,(
    ! [X6: $i] :
      ( v1_xboole_0 @ ( sk_B @ X6 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('124',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('125',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('126',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['123','128'])).

thf('130',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('131',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ( r1_yellow_0 @ X31 @ ( k5_waybel_0 @ X31 @ X30 ) )
      | ~ ( l1_orders_2 @ X31 )
      | ~ ( v5_orders_2 @ X31 )
      | ~ ( v4_orders_2 @ X31 )
      | ~ ( v3_orders_2 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_yellow_0 @ X0 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_yellow_0 @ X0 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_orders_2 @ X22 @ ( k1_yellow_0 @ X22 @ X23 ) @ ( k1_yellow_0 @ X22 @ X24 ) )
      | ~ ( r1_yellow_0 @ X22 @ X24 )
      | ~ ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_yellow_0 @ X22 @ X23 )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t34_yellow_0])).

thf('135',plain,(
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
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ X2 ) @ ( k1_yellow_0 @ X1 @ ( k5_waybel_0 @ X1 @ ( k1_yellow_0 @ X1 @ X0 ) ) ) )
      | ~ ( r1_tarski @ X2 @ ( k5_waybel_0 @ X1 @ ( k1_yellow_0 @ X1 @ X0 ) ) )
      | ~ ( r1_yellow_0 @ X1 @ X2 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ ( k5_waybel_0 @ X1 @ ( k1_yellow_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['129','136'])).

thf('138',plain,(
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
    inference('sup-',[status(thm)],['122','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ ( k5_waybel_0 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( v3_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['121','139'])).

thf('141',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['140','141','142','143','144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ! [X0: $i] :
        ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
        | ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( v4_orders_2 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['18','148'])).

thf('150',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['149','150','151','152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ! [X0: $i] :
        ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( k1_yellow_0 @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('158',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v13_waybel_0 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ( r2_hidden @ X28 @ X26 )
      | ~ ( r1_orders_2 @ X27 @ X29 @ X28 )
      | ~ ( r2_hidden @ X29 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['157','163'])).

thf('165',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('166',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['156','166'])).

thf('168',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','167'])).

thf('169',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['13','170'])).

thf('172',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X7 )
      | ( X8 = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('173',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B_1 )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['177'])).

thf('179',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['176','178'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('180',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_subset_1 @ X33 @ X32 )
      | ( X33 != X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('181',plain,(
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( v1_subset_1 @ X32 @ X32 ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('183',plain,(
    ! [X32: $i] :
      ~ ( v1_subset_1 @ X32 @ X32 ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','183'])).

thf('185',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['177'])).

thf('186',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33 = X32 )
      | ( v1_subset_1 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('188',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('190',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('191',plain,(
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('192',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['190','193'])).

thf('195',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('196',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['197','198'])).

thf('200',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['177'])).

thf('201',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','184','185','201'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gu9XS5qhKb
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.05/1.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.26  % Solved by: fo/fo7.sh
% 1.05/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.26  % done 1409 iterations in 0.805s
% 1.05/1.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.26  % SZS output start Refutation
% 1.05/1.26  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.05/1.26  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.05/1.26  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.05/1.26  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.05/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.26  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 1.05/1.26  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.05/1.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.26  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.05/1.26  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 1.05/1.26  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.05/1.26  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.05/1.26  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 1.05/1.26  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.05/1.26  thf(k5_waybel_0_type, type, k5_waybel_0: $i > $i > $i).
% 1.05/1.26  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.05/1.26  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 1.05/1.26  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 1.05/1.26  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 1.05/1.26  thf(sk_B_type, type, sk_B: $i > $i).
% 1.05/1.26  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.05/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.26  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.05/1.26  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 1.05/1.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.26  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 1.05/1.26  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.05/1.26  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.05/1.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.26  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.26  thf(t8_waybel_7, conjecture,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.05/1.26         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 1.05/1.26         ( l1_orders_2 @ A ) ) =>
% 1.05/1.26       ( ![B:$i]:
% 1.05/1.26         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 1.05/1.26             ( v13_waybel_0 @ B @ A ) & 
% 1.05/1.26             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.05/1.26           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 1.05/1.26             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 1.05/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.26    (~( ![A:$i]:
% 1.05/1.26        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.05/1.26            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 1.05/1.26            ( l1_orders_2 @ A ) ) =>
% 1.05/1.26          ( ![B:$i]:
% 1.05/1.26            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 1.05/1.26                ( v13_waybel_0 @ B @ A ) & 
% 1.05/1.26                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.05/1.26              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 1.05/1.26                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 1.05/1.26    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 1.05/1.26  thf('0', plain,
% 1.05/1.26      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 1.05/1.26        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('1', plain,
% 1.05/1.26      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 1.05/1.26       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('split', [status(esa)], ['0'])).
% 1.05/1.26  thf('2', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf(t49_subset_1, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.26       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 1.05/1.26         ( ( A ) = ( B ) ) ) ))).
% 1.05/1.26  thf('3', plain,
% 1.05/1.26      (![X7 : $i, X8 : $i]:
% 1.05/1.26         ((m1_subset_1 @ (sk_C_1 @ X7 @ X8) @ X8)
% 1.05/1.26          | ((X8) = (X7))
% 1.05/1.26          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.05/1.26      inference('cnf', [status(esa)], [t49_subset_1])).
% 1.05/1.26  thf('4', plain,
% 1.05/1.26      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 1.05/1.26        | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 1.05/1.26           (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['2', '3'])).
% 1.05/1.26  thf(t34_waybel_0, axiom,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.05/1.26         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.05/1.26       ( ![B:$i]:
% 1.05/1.26         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.05/1.26           ( ( r1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) ) & 
% 1.05/1.26             ( ( k1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 1.05/1.26  thf('5', plain,
% 1.05/1.26      (![X30 : $i, X31 : $i]:
% 1.05/1.26         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 1.05/1.26          | ((k1_yellow_0 @ X31 @ (k5_waybel_0 @ X31 @ X30)) = (X30))
% 1.05/1.26          | ~ (l1_orders_2 @ X31)
% 1.05/1.26          | ~ (v5_orders_2 @ X31)
% 1.05/1.26          | ~ (v4_orders_2 @ X31)
% 1.05/1.26          | ~ (v3_orders_2 @ X31)
% 1.05/1.26          | (v2_struct_0 @ X31))),
% 1.05/1.26      inference('cnf', [status(esa)], [t34_waybel_0])).
% 1.05/1.26  thf('6', plain,
% 1.05/1.26      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 1.05/1.26        | (v2_struct_0 @ sk_A)
% 1.05/1.26        | ~ (v3_orders_2 @ sk_A)
% 1.05/1.26        | ~ (v4_orders_2 @ sk_A)
% 1.05/1.26        | ~ (v5_orders_2 @ sk_A)
% 1.05/1.26        | ~ (l1_orders_2 @ sk_A)
% 1.05/1.26        | ((k1_yellow_0 @ sk_A @ 
% 1.05/1.26            (k5_waybel_0 @ sk_A @ (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 1.05/1.26            = (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['4', '5'])).
% 1.05/1.26  thf('7', plain, ((v3_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('9', plain, ((v5_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('11', plain,
% 1.05/1.26      ((((u1_struct_0 @ sk_A) = (sk_B_1))
% 1.05/1.26        | (v2_struct_0 @ sk_A)
% 1.05/1.26        | ((k1_yellow_0 @ sk_A @ 
% 1.05/1.26            (k5_waybel_0 @ sk_A @ (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 1.05/1.26            = (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 1.05/1.26      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 1.05/1.26  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('13', plain,
% 1.05/1.26      ((((k1_yellow_0 @ sk_A @ 
% 1.05/1.26          (k5_waybel_0 @ sk_A @ (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 1.05/1.26          = (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 1.05/1.26        | ((u1_struct_0 @ sk_A) = (sk_B_1)))),
% 1.05/1.26      inference('clc', [status(thm)], ['11', '12'])).
% 1.05/1.26  thf(dt_k1_yellow_0, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( l1_orders_2 @ A ) =>
% 1.05/1.26       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 1.05/1.26  thf('14', plain,
% 1.05/1.26      (![X19 : $i, X20 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ X19)
% 1.05/1.26          | (m1_subset_1 @ (k1_yellow_0 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 1.05/1.26      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 1.05/1.26  thf('15', plain,
% 1.05/1.26      (![X19 : $i, X20 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ X19)
% 1.05/1.26          | (m1_subset_1 @ (k1_yellow_0 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 1.05/1.26      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 1.05/1.26  thf('16', plain,
% 1.05/1.26      (![X30 : $i, X31 : $i]:
% 1.05/1.26         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 1.05/1.26          | ((k1_yellow_0 @ X31 @ (k5_waybel_0 @ X31 @ X30)) = (X30))
% 1.05/1.26          | ~ (l1_orders_2 @ X31)
% 1.05/1.26          | ~ (v5_orders_2 @ X31)
% 1.05/1.26          | ~ (v4_orders_2 @ X31)
% 1.05/1.26          | ~ (v3_orders_2 @ X31)
% 1.05/1.26          | (v2_struct_0 @ X31))),
% 1.05/1.26      inference('cnf', [status(esa)], [t34_waybel_0])).
% 1.05/1.26  thf('17', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ X0)
% 1.05/1.26          | (v2_struct_0 @ X0)
% 1.05/1.26          | ~ (v3_orders_2 @ X0)
% 1.05/1.26          | ~ (v4_orders_2 @ X0)
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | ((k1_yellow_0 @ X0 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1)))
% 1.05/1.26              = (k1_yellow_0 @ X0 @ X1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['15', '16'])).
% 1.05/1.26  thf('18', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (((k1_yellow_0 @ X0 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1)))
% 1.05/1.26            = (k1_yellow_0 @ X0 @ X1))
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | ~ (v4_orders_2 @ X0)
% 1.05/1.26          | ~ (v3_orders_2 @ X0)
% 1.05/1.26          | (v2_struct_0 @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['17'])).
% 1.05/1.26  thf(d11_yellow_0, axiom,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ( l1_orders_2 @ A ) =>
% 1.05/1.26       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 1.05/1.26  thf('19', plain,
% 1.05/1.26      (![X18 : $i]:
% 1.05/1.26         (((k3_yellow_0 @ X18) = (k1_yellow_0 @ X18 @ k1_xboole_0))
% 1.05/1.26          | ~ (l1_orders_2 @ X18))),
% 1.05/1.26      inference('cnf', [status(esa)], [d11_yellow_0])).
% 1.05/1.26  thf('20', plain,
% 1.05/1.26      (![X19 : $i, X20 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ X19)
% 1.05/1.26          | (m1_subset_1 @ (k1_yellow_0 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 1.05/1.26      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 1.05/1.26  thf('21', plain,
% 1.05/1.26      (![X18 : $i]:
% 1.05/1.26         (((k3_yellow_0 @ X18) = (k1_yellow_0 @ X18 @ k1_xboole_0))
% 1.05/1.26          | ~ (l1_orders_2 @ X18))),
% 1.05/1.26      inference('cnf', [status(esa)], [d11_yellow_0])).
% 1.05/1.26  thf(t42_yellow_0, axiom,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 1.05/1.26         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.05/1.26       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 1.05/1.26         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 1.05/1.26  thf('22', plain,
% 1.05/1.26      (![X25 : $i]:
% 1.05/1.26         ((r1_yellow_0 @ X25 @ k1_xboole_0)
% 1.05/1.26          | ~ (l1_orders_2 @ X25)
% 1.05/1.26          | ~ (v1_yellow_0 @ X25)
% 1.05/1.26          | ~ (v5_orders_2 @ X25)
% 1.05/1.26          | (v2_struct_0 @ X25))),
% 1.05/1.26      inference('cnf', [status(esa)], [t42_yellow_0])).
% 1.05/1.26  thf(d3_tarski, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( r1_tarski @ A @ B ) <=>
% 1.05/1.26       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.05/1.26  thf('23', plain,
% 1.05/1.26      (![X1 : $i, X3 : $i]:
% 1.05/1.26         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.05/1.26      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.26  thf('24', plain,
% 1.05/1.26      (![X1 : $i, X3 : $i]:
% 1.05/1.26         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.05/1.26      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.26  thf('25', plain,
% 1.05/1.26      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['23', '24'])).
% 1.05/1.26  thf('26', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.05/1.26      inference('simplify', [status(thm)], ['25'])).
% 1.05/1.26  thf('27', plain,
% 1.05/1.26      (![X25 : $i]:
% 1.05/1.26         ((r1_yellow_0 @ X25 @ k1_xboole_0)
% 1.05/1.26          | ~ (l1_orders_2 @ X25)
% 1.05/1.26          | ~ (v1_yellow_0 @ X25)
% 1.05/1.26          | ~ (v5_orders_2 @ X25)
% 1.05/1.26          | (v2_struct_0 @ X25))),
% 1.05/1.26      inference('cnf', [status(esa)], [t42_yellow_0])).
% 1.05/1.26  thf(t34_yellow_0, axiom,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ( l1_orders_2 @ A ) =>
% 1.05/1.26       ( ![B:$i,C:$i]:
% 1.05/1.26         ( ( ( r1_tarski @ B @ C ) & ( r1_yellow_0 @ A @ B ) & 
% 1.05/1.26             ( r1_yellow_0 @ A @ C ) ) =>
% 1.05/1.26           ( r1_orders_2 @
% 1.05/1.26             A @ ( k1_yellow_0 @ A @ B ) @ ( k1_yellow_0 @ A @ C ) ) ) ) ))).
% 1.05/1.26  thf('28', plain,
% 1.05/1.26      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.05/1.26         ((r1_orders_2 @ X22 @ (k1_yellow_0 @ X22 @ X23) @ 
% 1.05/1.26           (k1_yellow_0 @ X22 @ X24))
% 1.05/1.26          | ~ (r1_yellow_0 @ X22 @ X24)
% 1.05/1.26          | ~ (r1_tarski @ X23 @ X24)
% 1.05/1.26          | ~ (r1_yellow_0 @ X22 @ X23)
% 1.05/1.26          | ~ (l1_orders_2 @ X22))),
% 1.05/1.26      inference('cnf', [status(esa)], [t34_yellow_0])).
% 1.05/1.26  thf('29', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         ((v2_struct_0 @ X0)
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | ~ (v1_yellow_0 @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | ~ (r1_yellow_0 @ X0 @ X1)
% 1.05/1.26          | ~ (r1_tarski @ X1 @ k1_xboole_0)
% 1.05/1.26          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 1.05/1.26             (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['27', '28'])).
% 1.05/1.26  thf('30', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ 
% 1.05/1.26           (k1_yellow_0 @ X0 @ k1_xboole_0))
% 1.05/1.26          | ~ (r1_tarski @ X1 @ k1_xboole_0)
% 1.05/1.26          | ~ (r1_yellow_0 @ X0 @ X1)
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | ~ (v1_yellow_0 @ X0)
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | (v2_struct_0 @ X0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['29'])).
% 1.05/1.26  thf('31', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((v2_struct_0 @ X0)
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | ~ (v1_yellow_0 @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | ~ (r1_yellow_0 @ X0 @ k1_xboole_0)
% 1.05/1.26          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 1.05/1.26             (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['26', '30'])).
% 1.05/1.26  thf('32', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((v2_struct_0 @ X0)
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | ~ (v1_yellow_0 @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 1.05/1.26             (k1_yellow_0 @ X0 @ k1_xboole_0))
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | ~ (v1_yellow_0 @ X0)
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | (v2_struct_0 @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['22', '31'])).
% 1.05/1.26  thf('33', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 1.05/1.26           (k1_yellow_0 @ X0 @ k1_xboole_0))
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | ~ (v1_yellow_0 @ X0)
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | (v2_struct_0 @ X0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['32'])).
% 1.05/1.26  thf('34', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 1.05/1.26           (k1_yellow_0 @ X0 @ k1_xboole_0))
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | (v2_struct_0 @ X0)
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | ~ (v1_yellow_0 @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0))),
% 1.05/1.26      inference('sup+', [status(thm)], ['21', '33'])).
% 1.05/1.26  thf('35', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_yellow_0 @ X0)
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | (v2_struct_0 @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 1.05/1.26             (k1_yellow_0 @ X0 @ k1_xboole_0)))),
% 1.05/1.26      inference('simplify', [status(thm)], ['34'])).
% 1.05/1.26  thf(dt_k2_subset_1, axiom,
% 1.05/1.26    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.05/1.26  thf('36', plain,
% 1.05/1.26      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 1.05/1.26      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.05/1.26  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.05/1.26  thf('37', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 1.05/1.26      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.05/1.26  thf('38', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 1.05/1.26      inference('demod', [status(thm)], ['36', '37'])).
% 1.05/1.26  thf(d20_waybel_0, axiom,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ( l1_orders_2 @ A ) =>
% 1.05/1.26       ( ![B:$i]:
% 1.05/1.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.05/1.26           ( ( v13_waybel_0 @ B @ A ) <=>
% 1.05/1.26             ( ![C:$i]:
% 1.05/1.26               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.05/1.26                 ( ![D:$i]:
% 1.05/1.26                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.05/1.26                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 1.05/1.26                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 1.05/1.26  thf('39', plain,
% 1.05/1.26      (![X26 : $i, X27 : $i]:
% 1.05/1.26         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.05/1.26          | (r2_hidden @ (sk_C_2 @ X26 @ X27) @ X26)
% 1.05/1.26          | (v13_waybel_0 @ X26 @ X27)
% 1.05/1.26          | ~ (l1_orders_2 @ X27))),
% 1.05/1.26      inference('cnf', [status(esa)], [d20_waybel_0])).
% 1.05/1.26  thf('40', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ X0)
% 1.05/1.26          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.05/1.26          | (r2_hidden @ (sk_C_2 @ (u1_struct_0 @ X0) @ X0) @ 
% 1.05/1.26             (u1_struct_0 @ X0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['38', '39'])).
% 1.05/1.26  thf('41', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 1.05/1.26      inference('demod', [status(thm)], ['36', '37'])).
% 1.05/1.26  thf(t5_subset, axiom,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.05/1.26          ( v1_xboole_0 @ C ) ) ))).
% 1.05/1.26  thf('42', plain,
% 1.05/1.26      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X15 @ X16)
% 1.05/1.26          | ~ (v1_xboole_0 @ X17)
% 1.05/1.26          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.05/1.26      inference('cnf', [status(esa)], [t5_subset])).
% 1.05/1.26  thf('43', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['41', '42'])).
% 1.05/1.26  thf('44', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['40', '43'])).
% 1.05/1.26  thf('45', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 1.05/1.26      inference('demod', [status(thm)], ['36', '37'])).
% 1.05/1.26  thf('46', plain,
% 1.05/1.26      (![X26 : $i, X27 : $i]:
% 1.05/1.26         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.05/1.26          | (m1_subset_1 @ (sk_D @ X26 @ X27) @ (u1_struct_0 @ X27))
% 1.05/1.26          | (v13_waybel_0 @ X26 @ X27)
% 1.05/1.26          | ~ (l1_orders_2 @ X27))),
% 1.05/1.26      inference('cnf', [status(esa)], [d20_waybel_0])).
% 1.05/1.26  thf('47', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ X0)
% 1.05/1.26          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.05/1.26          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0) @ 
% 1.05/1.26             (u1_struct_0 @ X0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['45', '46'])).
% 1.05/1.26  thf(t2_subset, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( m1_subset_1 @ A @ B ) =>
% 1.05/1.26       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.05/1.26  thf('48', plain,
% 1.05/1.26      (![X10 : $i, X11 : $i]:
% 1.05/1.26         ((r2_hidden @ X10 @ X11)
% 1.05/1.26          | (v1_xboole_0 @ X11)
% 1.05/1.26          | ~ (m1_subset_1 @ X10 @ X11))),
% 1.05/1.26      inference('cnf', [status(esa)], [t2_subset])).
% 1.05/1.26  thf('49', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.05/1.26          | (r2_hidden @ (sk_D @ (u1_struct_0 @ X0) @ X0) @ (u1_struct_0 @ X0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['47', '48'])).
% 1.05/1.26  thf('50', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 1.05/1.26      inference('demod', [status(thm)], ['36', '37'])).
% 1.05/1.26  thf('51', plain,
% 1.05/1.26      (![X26 : $i, X27 : $i]:
% 1.05/1.26         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.05/1.26          | ~ (r2_hidden @ (sk_D @ X26 @ X27) @ X26)
% 1.05/1.26          | (v13_waybel_0 @ X26 @ X27)
% 1.05/1.26          | ~ (l1_orders_2 @ X27))),
% 1.05/1.26      inference('cnf', [status(esa)], [d20_waybel_0])).
% 1.05/1.26  thf('52', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ X0)
% 1.05/1.26          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.05/1.26          | ~ (r2_hidden @ (sk_D @ (u1_struct_0 @ X0) @ X0) @ 
% 1.05/1.26               (u1_struct_0 @ X0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['50', '51'])).
% 1.05/1.26  thf('53', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.05/1.26          | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['49', '52'])).
% 1.05/1.26  thf('54', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((v13_waybel_0 @ (u1_struct_0 @ X0) @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.05/1.26      inference('simplify', [status(thm)], ['53'])).
% 1.05/1.26  thf('55', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ X0) | (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0))),
% 1.05/1.26      inference('clc', [status(thm)], ['44', '54'])).
% 1.05/1.26  thf('56', plain,
% 1.05/1.26      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('split', [status(esa)], ['0'])).
% 1.05/1.26  thf('57', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf(t4_subset, axiom,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.05/1.26       ( m1_subset_1 @ A @ C ) ))).
% 1.05/1.26  thf('58', plain,
% 1.05/1.26      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X12 @ X13)
% 1.05/1.26          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.05/1.26          | (m1_subset_1 @ X12 @ X14))),
% 1.05/1.26      inference('cnf', [status(esa)], [t4_subset])).
% 1.05/1.26  thf('59', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.05/1.26      inference('sup-', [status(thm)], ['57', '58'])).
% 1.05/1.26  thf('60', plain,
% 1.05/1.26      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['56', '59'])).
% 1.05/1.26  thf('61', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 1.05/1.26      inference('demod', [status(thm)], ['36', '37'])).
% 1.05/1.26  thf('62', plain,
% 1.05/1.26      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.05/1.26         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.05/1.26          | ~ (v13_waybel_0 @ X26 @ X27)
% 1.05/1.26          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 1.05/1.26          | (r2_hidden @ X28 @ X26)
% 1.05/1.26          | ~ (r1_orders_2 @ X27 @ X29 @ X28)
% 1.05/1.26          | ~ (r2_hidden @ X29 @ X26)
% 1.05/1.26          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 1.05/1.26          | ~ (l1_orders_2 @ X27))),
% 1.05/1.26      inference('cnf', [status(esa)], [d20_waybel_0])).
% 1.05/1.26  thf('63', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ X0)
% 1.05/1.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 1.05/1.26          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 1.05/1.26          | ~ (r1_orders_2 @ X0 @ X1 @ X2)
% 1.05/1.26          | (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 1.05/1.26          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.05/1.26          | ~ (v13_waybel_0 @ (u1_struct_0 @ X0) @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['61', '62'])).
% 1.05/1.26  thf('64', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          (~ (v13_waybel_0 @ (u1_struct_0 @ sk_A) @ sk_A)
% 1.05/1.26           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 1.05/1.26           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.05/1.26           | ~ (l1_orders_2 @ sk_A)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['60', '63'])).
% 1.05/1.26  thf('65', plain,
% 1.05/1.26      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('split', [status(esa)], ['0'])).
% 1.05/1.26  thf('66', plain,
% 1.05/1.26      (![X1 : $i, X3 : $i]:
% 1.05/1.26         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.05/1.26      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.26  thf('67', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.05/1.26      inference('sup-', [status(thm)], ['57', '58'])).
% 1.05/1.26  thf('68', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((r1_tarski @ sk_B_1 @ X0)
% 1.05/1.26          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['66', '67'])).
% 1.05/1.26  thf('69', plain,
% 1.05/1.26      (![X10 : $i, X11 : $i]:
% 1.05/1.26         ((r2_hidden @ X10 @ X11)
% 1.05/1.26          | (v1_xboole_0 @ X11)
% 1.05/1.26          | ~ (m1_subset_1 @ X10 @ X11))),
% 1.05/1.26      inference('cnf', [status(esa)], [t2_subset])).
% 1.05/1.26  thf('70', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((r1_tarski @ sk_B_1 @ X0)
% 1.05/1.26          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['68', '69'])).
% 1.05/1.26  thf('71', plain,
% 1.05/1.26      (![X1 : $i, X3 : $i]:
% 1.05/1.26         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.05/1.26      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.26  thf('72', plain,
% 1.05/1.26      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26        | (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 1.05/1.26        | (r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['70', '71'])).
% 1.05/1.26  thf('73', plain,
% 1.05/1.26      (((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 1.05/1.26        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('simplify', [status(thm)], ['72'])).
% 1.05/1.26  thf('74', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X0 @ X1)
% 1.05/1.26          | (r2_hidden @ X0 @ X2)
% 1.05/1.26          | ~ (r1_tarski @ X1 @ X2))),
% 1.05/1.26      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.26  thf('75', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26          | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.05/1.26      inference('sup-', [status(thm)], ['73', '74'])).
% 1.05/1.26  thf('76', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('77', plain,
% 1.05/1.26      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X15 @ X16)
% 1.05/1.26          | ~ (v1_xboole_0 @ X17)
% 1.05/1.26          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.05/1.26      inference('cnf', [status(esa)], [t5_subset])).
% 1.05/1.26  thf('78', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.05/1.26      inference('sup-', [status(thm)], ['76', '77'])).
% 1.05/1.26  thf('79', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X0 @ sk_B_1) | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('clc', [status(thm)], ['75', '78'])).
% 1.05/1.26  thf('80', plain,
% 1.05/1.26      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['65', '79'])).
% 1.05/1.26  thf('81', plain, ((l1_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('82', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          (~ (v13_waybel_0 @ (u1_struct_0 @ sk_A) @ sk_A)
% 1.05/1.26           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('demod', [status(thm)], ['64', '80', '81'])).
% 1.05/1.26  thf('83', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          (~ (l1_orders_2 @ sk_A)
% 1.05/1.26           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 1.05/1.26           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['55', '82'])).
% 1.05/1.26  thf('84', plain, ((l1_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('85', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          (~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 1.05/1.26           | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('demod', [status(thm)], ['83', '84'])).
% 1.05/1.26  thf('86', plain,
% 1.05/1.26      (((~ (l1_orders_2 @ sk_A)
% 1.05/1.26         | (v2_struct_0 @ sk_A)
% 1.05/1.26         | ~ (v5_orders_2 @ sk_A)
% 1.05/1.26         | ~ (v1_yellow_0 @ sk_A)
% 1.05/1.26         | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 1.05/1.26              (u1_struct_0 @ sk_A))
% 1.05/1.26         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 1.05/1.26            (u1_struct_0 @ sk_A))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['35', '85'])).
% 1.05/1.26  thf('87', plain, ((l1_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('88', plain, ((v5_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('89', plain, ((v1_yellow_0 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('90', plain,
% 1.05/1.26      ((((v2_struct_0 @ sk_A)
% 1.05/1.26         | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 1.05/1.26              (u1_struct_0 @ sk_A))
% 1.05/1.26         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 1.05/1.26            (u1_struct_0 @ sk_A))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 1.05/1.26  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('92', plain,
% 1.05/1.26      ((((r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ (u1_struct_0 @ sk_A))
% 1.05/1.26         | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 1.05/1.26              (u1_struct_0 @ sk_A))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('clc', [status(thm)], ['90', '91'])).
% 1.05/1.26  thf('93', plain,
% 1.05/1.26      (((~ (l1_orders_2 @ sk_A)
% 1.05/1.26         | (r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 1.05/1.26            (u1_struct_0 @ sk_A))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['20', '92'])).
% 1.05/1.26  thf('94', plain, ((l1_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('95', plain,
% 1.05/1.26      (((r2_hidden @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ (u1_struct_0 @ sk_A)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('demod', [status(thm)], ['93', '94'])).
% 1.05/1.26  thf('96', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 1.05/1.26      inference('demod', [status(thm)], ['36', '37'])).
% 1.05/1.26  thf('97', plain,
% 1.05/1.26      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X12 @ X13)
% 1.05/1.26          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.05/1.26          | (m1_subset_1 @ X12 @ X14))),
% 1.05/1.26      inference('cnf', [status(esa)], [t4_subset])).
% 1.05/1.26  thf('98', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['96', '97'])).
% 1.05/1.26  thf('99', plain,
% 1.05/1.26      (((m1_subset_1 @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 1.05/1.26         (u1_struct_0 @ sk_A)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['95', '98'])).
% 1.05/1.26  thf('100', plain,
% 1.05/1.26      (![X30 : $i, X31 : $i]:
% 1.05/1.26         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 1.05/1.26          | ((k1_yellow_0 @ X31 @ (k5_waybel_0 @ X31 @ X30)) = (X30))
% 1.05/1.26          | ~ (l1_orders_2 @ X31)
% 1.05/1.26          | ~ (v5_orders_2 @ X31)
% 1.05/1.26          | ~ (v4_orders_2 @ X31)
% 1.05/1.26          | ~ (v3_orders_2 @ X31)
% 1.05/1.26          | (v2_struct_0 @ X31))),
% 1.05/1.26      inference('cnf', [status(esa)], [t34_waybel_0])).
% 1.05/1.26  thf('101', plain,
% 1.05/1.26      ((((v2_struct_0 @ sk_A)
% 1.05/1.26         | ~ (v3_orders_2 @ sk_A)
% 1.05/1.26         | ~ (v4_orders_2 @ sk_A)
% 1.05/1.26         | ~ (v5_orders_2 @ sk_A)
% 1.05/1.26         | ~ (l1_orders_2 @ sk_A)
% 1.05/1.26         | ((k1_yellow_0 @ sk_A @ 
% 1.05/1.26             (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 1.05/1.26             = (k1_yellow_0 @ sk_A @ k1_xboole_0))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['99', '100'])).
% 1.05/1.26  thf('102', plain, ((v3_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('103', plain, ((v4_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('104', plain, ((v5_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('105', plain, ((l1_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('106', plain,
% 1.05/1.26      ((((v2_struct_0 @ sk_A)
% 1.05/1.26         | ((k1_yellow_0 @ sk_A @ 
% 1.05/1.26             (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 1.05/1.26             = (k1_yellow_0 @ sk_A @ k1_xboole_0))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 1.05/1.26  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('108', plain,
% 1.05/1.26      ((((k1_yellow_0 @ sk_A @ 
% 1.05/1.26          (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 1.05/1.26          = (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('clc', [status(thm)], ['106', '107'])).
% 1.05/1.26  thf('109', plain,
% 1.05/1.26      (((((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ (k3_yellow_0 @ sk_A)))
% 1.05/1.26           = (k1_yellow_0 @ sk_A @ k1_xboole_0))
% 1.05/1.26         | ~ (l1_orders_2 @ sk_A)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup+', [status(thm)], ['19', '108'])).
% 1.05/1.26  thf('110', plain,
% 1.05/1.26      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['56', '59'])).
% 1.05/1.26  thf('111', plain,
% 1.05/1.26      (![X30 : $i, X31 : $i]:
% 1.05/1.26         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 1.05/1.26          | ((k1_yellow_0 @ X31 @ (k5_waybel_0 @ X31 @ X30)) = (X30))
% 1.05/1.26          | ~ (l1_orders_2 @ X31)
% 1.05/1.26          | ~ (v5_orders_2 @ X31)
% 1.05/1.26          | ~ (v4_orders_2 @ X31)
% 1.05/1.26          | ~ (v3_orders_2 @ X31)
% 1.05/1.26          | (v2_struct_0 @ X31))),
% 1.05/1.26      inference('cnf', [status(esa)], [t34_waybel_0])).
% 1.05/1.26  thf('112', plain,
% 1.05/1.26      ((((v2_struct_0 @ sk_A)
% 1.05/1.26         | ~ (v3_orders_2 @ sk_A)
% 1.05/1.26         | ~ (v4_orders_2 @ sk_A)
% 1.05/1.26         | ~ (v5_orders_2 @ sk_A)
% 1.05/1.26         | ~ (l1_orders_2 @ sk_A)
% 1.05/1.26         | ((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ (k3_yellow_0 @ sk_A)))
% 1.05/1.26             = (k3_yellow_0 @ sk_A))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['110', '111'])).
% 1.05/1.26  thf('113', plain, ((v3_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('114', plain, ((v4_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('115', plain, ((v5_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('116', plain, ((l1_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('117', plain,
% 1.05/1.26      ((((v2_struct_0 @ sk_A)
% 1.05/1.26         | ((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ (k3_yellow_0 @ sk_A)))
% 1.05/1.26             = (k3_yellow_0 @ sk_A))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 1.05/1.26  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('119', plain,
% 1.05/1.26      ((((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ (k3_yellow_0 @ sk_A)))
% 1.05/1.26          = (k3_yellow_0 @ sk_A)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('clc', [status(thm)], ['117', '118'])).
% 1.05/1.26  thf('120', plain, ((l1_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('121', plain,
% 1.05/1.26      ((((k3_yellow_0 @ sk_A) = (k1_yellow_0 @ sk_A @ k1_xboole_0)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('demod', [status(thm)], ['109', '119', '120'])).
% 1.05/1.26  thf('122', plain,
% 1.05/1.26      (![X25 : $i]:
% 1.05/1.26         ((r1_yellow_0 @ X25 @ k1_xboole_0)
% 1.05/1.26          | ~ (l1_orders_2 @ X25)
% 1.05/1.26          | ~ (v1_yellow_0 @ X25)
% 1.05/1.26          | ~ (v5_orders_2 @ X25)
% 1.05/1.26          | (v2_struct_0 @ X25))),
% 1.05/1.26      inference('cnf', [status(esa)], [t42_yellow_0])).
% 1.05/1.26  thf(rc2_subset_1, axiom,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ?[B:$i]:
% 1.05/1.26       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.05/1.26  thf('123', plain, (![X6 : $i]: (v1_xboole_0 @ (sk_B @ X6))),
% 1.05/1.26      inference('cnf', [status(esa)], [rc2_subset_1])).
% 1.05/1.26  thf('124', plain,
% 1.05/1.26      (![X1 : $i, X3 : $i]:
% 1.05/1.26         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.05/1.26      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.26  thf(t4_subset_1, axiom,
% 1.05/1.26    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.05/1.26  thf('125', plain,
% 1.05/1.26      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 1.05/1.26      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.05/1.26  thf('126', plain,
% 1.05/1.26      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X15 @ X16)
% 1.05/1.26          | ~ (v1_xboole_0 @ X17)
% 1.05/1.26          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.05/1.26      inference('cnf', [status(esa)], [t5_subset])).
% 1.05/1.26  thf('127', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['125', '126'])).
% 1.05/1.26  thf('128', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         ((r1_tarski @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.05/1.26      inference('sup-', [status(thm)], ['124', '127'])).
% 1.05/1.26  thf('129', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 1.05/1.26      inference('sup-', [status(thm)], ['123', '128'])).
% 1.05/1.26  thf('130', plain,
% 1.05/1.26      (![X19 : $i, X20 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ X19)
% 1.05/1.26          | (m1_subset_1 @ (k1_yellow_0 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 1.05/1.26      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 1.05/1.26  thf('131', plain,
% 1.05/1.26      (![X30 : $i, X31 : $i]:
% 1.05/1.26         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 1.05/1.26          | (r1_yellow_0 @ X31 @ (k5_waybel_0 @ X31 @ X30))
% 1.05/1.26          | ~ (l1_orders_2 @ X31)
% 1.05/1.26          | ~ (v5_orders_2 @ X31)
% 1.05/1.26          | ~ (v4_orders_2 @ X31)
% 1.05/1.26          | ~ (v3_orders_2 @ X31)
% 1.05/1.26          | (v2_struct_0 @ X31))),
% 1.05/1.26      inference('cnf', [status(esa)], [t34_waybel_0])).
% 1.05/1.26  thf('132', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ X0)
% 1.05/1.26          | (v2_struct_0 @ X0)
% 1.05/1.26          | ~ (v3_orders_2 @ X0)
% 1.05/1.26          | ~ (v4_orders_2 @ X0)
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | (r1_yellow_0 @ X0 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['130', '131'])).
% 1.05/1.26  thf('133', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         ((r1_yellow_0 @ X0 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1)))
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | ~ (v4_orders_2 @ X0)
% 1.05/1.26          | ~ (v3_orders_2 @ X0)
% 1.05/1.26          | (v2_struct_0 @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['132'])).
% 1.05/1.26  thf('134', plain,
% 1.05/1.26      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.05/1.26         ((r1_orders_2 @ X22 @ (k1_yellow_0 @ X22 @ X23) @ 
% 1.05/1.26           (k1_yellow_0 @ X22 @ X24))
% 1.05/1.26          | ~ (r1_yellow_0 @ X22 @ X24)
% 1.05/1.26          | ~ (r1_tarski @ X23 @ X24)
% 1.05/1.26          | ~ (r1_yellow_0 @ X22 @ X23)
% 1.05/1.26          | ~ (l1_orders_2 @ X22))),
% 1.05/1.26      inference('cnf', [status(esa)], [t34_yellow_0])).
% 1.05/1.26  thf('135', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ X1)
% 1.05/1.26          | (v2_struct_0 @ X1)
% 1.05/1.26          | ~ (v3_orders_2 @ X1)
% 1.05/1.26          | ~ (v4_orders_2 @ X1)
% 1.05/1.26          | ~ (v5_orders_2 @ X1)
% 1.05/1.26          | ~ (l1_orders_2 @ X1)
% 1.05/1.26          | ~ (r1_yellow_0 @ X1 @ X2)
% 1.05/1.26          | ~ (r1_tarski @ X2 @ (k5_waybel_0 @ X1 @ (k1_yellow_0 @ X1 @ X0)))
% 1.05/1.26          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ X2) @ 
% 1.05/1.26             (k1_yellow_0 @ X1 @ (k5_waybel_0 @ X1 @ (k1_yellow_0 @ X1 @ X0)))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['133', '134'])).
% 1.05/1.26  thf('136', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.26         ((r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ X2) @ 
% 1.05/1.26           (k1_yellow_0 @ X1 @ (k5_waybel_0 @ X1 @ (k1_yellow_0 @ X1 @ X0))))
% 1.05/1.26          | ~ (r1_tarski @ X2 @ (k5_waybel_0 @ X1 @ (k1_yellow_0 @ X1 @ X0)))
% 1.05/1.26          | ~ (r1_yellow_0 @ X1 @ X2)
% 1.05/1.26          | ~ (v5_orders_2 @ X1)
% 1.05/1.26          | ~ (v4_orders_2 @ X1)
% 1.05/1.26          | ~ (v3_orders_2 @ X1)
% 1.05/1.26          | (v2_struct_0 @ X1)
% 1.05/1.26          | ~ (l1_orders_2 @ X1))),
% 1.05/1.26      inference('simplify', [status(thm)], ['135'])).
% 1.05/1.26  thf('137', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ X1)
% 1.05/1.26          | (v2_struct_0 @ X1)
% 1.05/1.26          | ~ (v3_orders_2 @ X1)
% 1.05/1.26          | ~ (v4_orders_2 @ X1)
% 1.05/1.26          | ~ (v5_orders_2 @ X1)
% 1.05/1.26          | ~ (r1_yellow_0 @ X1 @ k1_xboole_0)
% 1.05/1.26          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 1.05/1.26             (k1_yellow_0 @ X1 @ (k5_waybel_0 @ X1 @ (k1_yellow_0 @ X1 @ X0)))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['129', '136'])).
% 1.05/1.26  thf('138', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         ((v2_struct_0 @ X0)
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | ~ (v1_yellow_0 @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 1.05/1.26             (k1_yellow_0 @ X0 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1))))
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | ~ (v4_orders_2 @ X0)
% 1.05/1.26          | ~ (v3_orders_2 @ X0)
% 1.05/1.26          | (v2_struct_0 @ X0)
% 1.05/1.26          | ~ (l1_orders_2 @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['122', '137'])).
% 1.05/1.26  thf('139', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (v3_orders_2 @ X0)
% 1.05/1.26          | ~ (v4_orders_2 @ X0)
% 1.05/1.26          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 1.05/1.26             (k1_yellow_0 @ X0 @ (k5_waybel_0 @ X0 @ (k1_yellow_0 @ X0 @ X1))))
% 1.05/1.26          | ~ (l1_orders_2 @ X0)
% 1.05/1.26          | ~ (v1_yellow_0 @ X0)
% 1.05/1.26          | ~ (v5_orders_2 @ X0)
% 1.05/1.26          | (v2_struct_0 @ X0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['138'])).
% 1.05/1.26  thf('140', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          ((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 1.05/1.26            (k1_yellow_0 @ sk_A @ 
% 1.05/1.26             (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ X0))))
% 1.05/1.26           | (v2_struct_0 @ sk_A)
% 1.05/1.26           | ~ (v5_orders_2 @ sk_A)
% 1.05/1.26           | ~ (v1_yellow_0 @ sk_A)
% 1.05/1.26           | ~ (l1_orders_2 @ sk_A)
% 1.05/1.26           | ~ (v4_orders_2 @ sk_A)
% 1.05/1.26           | ~ (v3_orders_2 @ sk_A)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup+', [status(thm)], ['121', '139'])).
% 1.05/1.26  thf('141', plain, ((v5_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('142', plain, ((v1_yellow_0 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('143', plain, ((l1_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('144', plain, ((v4_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('145', plain, ((v3_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('146', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          ((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 1.05/1.26            (k1_yellow_0 @ sk_A @ 
% 1.05/1.26             (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ X0))))
% 1.05/1.26           | (v2_struct_0 @ sk_A)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('demod', [status(thm)],
% 1.05/1.26                ['140', '141', '142', '143', '144', '145'])).
% 1.05/1.26  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('148', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 1.05/1.26           (k1_yellow_0 @ sk_A @ 
% 1.05/1.26            (k5_waybel_0 @ sk_A @ (k1_yellow_0 @ sk_A @ X0)))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('clc', [status(thm)], ['146', '147'])).
% 1.05/1.26  thf('149', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          ((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 1.05/1.26            (k1_yellow_0 @ sk_A @ X0))
% 1.05/1.26           | ~ (l1_orders_2 @ sk_A)
% 1.05/1.26           | (v2_struct_0 @ sk_A)
% 1.05/1.26           | ~ (v3_orders_2 @ sk_A)
% 1.05/1.26           | ~ (v4_orders_2 @ sk_A)
% 1.05/1.26           | ~ (v5_orders_2 @ sk_A)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup+', [status(thm)], ['18', '148'])).
% 1.05/1.26  thf('150', plain, ((l1_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('151', plain, ((v3_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('152', plain, ((v4_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('153', plain, ((v5_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('154', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          ((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 1.05/1.26            (k1_yellow_0 @ sk_A @ X0))
% 1.05/1.26           | (v2_struct_0 @ sk_A)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('demod', [status(thm)], ['149', '150', '151', '152', '153'])).
% 1.05/1.26  thf('155', plain, (~ (v2_struct_0 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('156', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 1.05/1.26           (k1_yellow_0 @ sk_A @ X0)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('clc', [status(thm)], ['154', '155'])).
% 1.05/1.26  thf('157', plain,
% 1.05/1.26      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['56', '59'])).
% 1.05/1.26  thf('158', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('159', plain,
% 1.05/1.26      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.05/1.26         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.05/1.26          | ~ (v13_waybel_0 @ X26 @ X27)
% 1.05/1.26          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 1.05/1.26          | (r2_hidden @ X28 @ X26)
% 1.05/1.26          | ~ (r1_orders_2 @ X27 @ X29 @ X28)
% 1.05/1.26          | ~ (r2_hidden @ X29 @ X26)
% 1.05/1.26          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X27))
% 1.05/1.26          | ~ (l1_orders_2 @ X27))),
% 1.05/1.26      inference('cnf', [status(esa)], [d20_waybel_0])).
% 1.05/1.26  thf('160', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ sk_A)
% 1.05/1.26          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.05/1.26          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 1.05/1.26          | (r2_hidden @ X1 @ sk_B_1)
% 1.05/1.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.05/1.26          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 1.05/1.26      inference('sup-', [status(thm)], ['158', '159'])).
% 1.05/1.26  thf('161', plain, ((l1_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('162', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('163', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.05/1.26          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 1.05/1.26          | (r2_hidden @ X1 @ sk_B_1)
% 1.05/1.26          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('demod', [status(thm)], ['160', '161', '162'])).
% 1.05/1.26  thf('164', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26           | (r2_hidden @ X0 @ sk_B_1)
% 1.05/1.26           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 1.05/1.26           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['157', '163'])).
% 1.05/1.26  thf('165', plain,
% 1.05/1.26      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('split', [status(esa)], ['0'])).
% 1.05/1.26  thf('166', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26           | (r2_hidden @ X0 @ sk_B_1)
% 1.05/1.26           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('demod', [status(thm)], ['164', '165'])).
% 1.05/1.26  thf('167', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          ((r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 1.05/1.26           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['156', '166'])).
% 1.05/1.26  thf('168', plain,
% 1.05/1.26      ((![X0 : $i]:
% 1.05/1.26          (~ (l1_orders_2 @ sk_A)
% 1.05/1.26           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['14', '167'])).
% 1.05/1.26  thf('169', plain, ((l1_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('170', plain,
% 1.05/1.26      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('demod', [status(thm)], ['168', '169'])).
% 1.05/1.26  thf('171', plain,
% 1.05/1.26      ((((r2_hidden @ (sk_C_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ sk_B_1)
% 1.05/1.26         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup+', [status(thm)], ['13', '170'])).
% 1.05/1.26  thf('172', plain,
% 1.05/1.26      (![X7 : $i, X8 : $i]:
% 1.05/1.26         (~ (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X7)
% 1.05/1.26          | ((X8) = (X7))
% 1.05/1.26          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.05/1.26      inference('cnf', [status(esa)], [t49_subset_1])).
% 1.05/1.26  thf('173', plain,
% 1.05/1.26      (((((u1_struct_0 @ sk_A) = (sk_B_1))
% 1.05/1.26         | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.05/1.26         | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['171', '172'])).
% 1.05/1.26  thf('174', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('175', plain,
% 1.05/1.26      (((((u1_struct_0 @ sk_A) = (sk_B_1)) | ((u1_struct_0 @ sk_A) = (sk_B_1))))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('demod', [status(thm)], ['173', '174'])).
% 1.05/1.26  thf('176', plain,
% 1.05/1.26      ((((u1_struct_0 @ sk_A) = (sk_B_1)))
% 1.05/1.26         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('simplify', [status(thm)], ['175'])).
% 1.05/1.26  thf('177', plain,
% 1.05/1.26      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 1.05/1.26        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('178', plain,
% 1.05/1.26      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 1.05/1.26         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 1.05/1.26      inference('split', [status(esa)], ['177'])).
% 1.05/1.26  thf('179', plain,
% 1.05/1.26      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 1.05/1.26         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 1.05/1.26             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('sup+', [status(thm)], ['176', '178'])).
% 1.05/1.26  thf(d7_subset_1, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.26       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 1.05/1.26  thf('180', plain,
% 1.05/1.26      (![X32 : $i, X33 : $i]:
% 1.05/1.26         (~ (v1_subset_1 @ X33 @ X32)
% 1.05/1.26          | ((X33) != (X32))
% 1.05/1.26          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 1.05/1.26      inference('cnf', [status(esa)], [d7_subset_1])).
% 1.05/1.26  thf('181', plain,
% 1.05/1.26      (![X32 : $i]:
% 1.05/1.26         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X32))
% 1.05/1.26          | ~ (v1_subset_1 @ X32 @ X32))),
% 1.05/1.26      inference('simplify', [status(thm)], ['180'])).
% 1.05/1.26  thf('182', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 1.05/1.26      inference('demod', [status(thm)], ['36', '37'])).
% 1.05/1.26  thf('183', plain, (![X32 : $i]: ~ (v1_subset_1 @ X32 @ X32)),
% 1.05/1.26      inference('demod', [status(thm)], ['181', '182'])).
% 1.05/1.26  thf('184', plain,
% 1.05/1.26      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 1.05/1.26       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['179', '183'])).
% 1.05/1.26  thf('185', plain,
% 1.05/1.26      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 1.05/1.26       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('split', [status(esa)], ['177'])).
% 1.05/1.26  thf('186', plain,
% 1.05/1.26      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('187', plain,
% 1.05/1.26      (![X32 : $i, X33 : $i]:
% 1.05/1.26         (((X33) = (X32))
% 1.05/1.26          | (v1_subset_1 @ X33 @ X32)
% 1.05/1.26          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 1.05/1.26      inference('cnf', [status(esa)], [d7_subset_1])).
% 1.05/1.26  thf('188', plain,
% 1.05/1.26      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 1.05/1.26        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['186', '187'])).
% 1.05/1.26  thf('189', plain,
% 1.05/1.26      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 1.05/1.26         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 1.05/1.26      inference('split', [status(esa)], ['0'])).
% 1.05/1.26  thf('190', plain,
% 1.05/1.26      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 1.05/1.26         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['188', '189'])).
% 1.05/1.26  thf(dt_k3_yellow_0, axiom,
% 1.05/1.26    (![A:$i]:
% 1.05/1.26     ( ( l1_orders_2 @ A ) =>
% 1.05/1.26       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 1.05/1.26  thf('191', plain,
% 1.05/1.26      (![X21 : $i]:
% 1.05/1.26         ((m1_subset_1 @ (k3_yellow_0 @ X21) @ (u1_struct_0 @ X21))
% 1.05/1.26          | ~ (l1_orders_2 @ X21))),
% 1.05/1.26      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 1.05/1.26  thf('192', plain,
% 1.05/1.26      (![X10 : $i, X11 : $i]:
% 1.05/1.26         ((r2_hidden @ X10 @ X11)
% 1.05/1.26          | (v1_xboole_0 @ X11)
% 1.05/1.26          | ~ (m1_subset_1 @ X10 @ X11))),
% 1.05/1.26      inference('cnf', [status(esa)], [t2_subset])).
% 1.05/1.26  thf('193', plain,
% 1.05/1.26      (![X0 : $i]:
% 1.05/1.26         (~ (l1_orders_2 @ X0)
% 1.05/1.26          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.05/1.26          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['191', '192'])).
% 1.05/1.26  thf('194', plain,
% 1.05/1.26      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 1.05/1.26         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.05/1.26         | ~ (l1_orders_2 @ sk_A)))
% 1.05/1.26         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 1.05/1.26      inference('sup+', [status(thm)], ['190', '193'])).
% 1.05/1.26  thf('195', plain,
% 1.05/1.26      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 1.05/1.26         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['188', '189'])).
% 1.05/1.26  thf('196', plain, ((l1_orders_2 @ sk_A)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('197', plain,
% 1.05/1.26      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1) | (v1_xboole_0 @ sk_B_1)))
% 1.05/1.26         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 1.05/1.26      inference('demod', [status(thm)], ['194', '195', '196'])).
% 1.05/1.26  thf('198', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('199', plain,
% 1.05/1.26      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 1.05/1.26         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 1.05/1.26      inference('clc', [status(thm)], ['197', '198'])).
% 1.05/1.26  thf('200', plain,
% 1.05/1.26      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 1.05/1.26         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 1.05/1.26      inference('split', [status(esa)], ['177'])).
% 1.05/1.26  thf('201', plain,
% 1.05/1.26      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 1.05/1.26       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['199', '200'])).
% 1.05/1.26  thf('202', plain, ($false),
% 1.05/1.26      inference('sat_resolution*', [status(thm)], ['1', '184', '185', '201'])).
% 1.05/1.26  
% 1.05/1.26  % SZS output end Refutation
% 1.05/1.26  
% 1.05/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
