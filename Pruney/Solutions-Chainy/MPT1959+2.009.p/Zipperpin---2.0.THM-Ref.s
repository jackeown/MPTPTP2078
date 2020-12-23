%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X5VexINtTq

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:10 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 191 expanded)
%              Number of leaves         :   39 (  71 expanded)
%              Depth                    :   22
%              Number of atoms          : 1145 (2582 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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
      ( ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('5',plain,(
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

thf('6',plain,(
    ! [X24: $i] :
      ( ( r1_yellow_0 @ X24 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v1_yellow_0 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( r2_lattice3 @ X26 @ k1_xboole_0 @ X25 )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
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

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X20
       != ( k1_yellow_0 @ X18 @ X19 ) )
      | ~ ( r2_lattice3 @ X18 @ X19 @ X21 )
      | ( r1_orders_2 @ X18 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('13',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ( r1_orders_2 @ X18 @ ( k1_yellow_0 @ X18 @ X19 ) @ X21 )
      | ~ ( r2_lattice3 @ X18 @ X19 @ X21 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 )
      | ~ ( r1_yellow_0 @ X0 @ k1_xboole_0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r1_yellow_0 @ X0 @ k1_xboole_0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v13_waybel_0 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( r2_hidden @ X29 @ X27 )
      | ~ ( r1_orders_2 @ X28 @ X30 @ X29 )
      | ~ ( r2_hidden @ X30 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_orders_2 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
        | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','45'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
        | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,
    ( ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['56','58'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('60',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_subset_1 @ X32 @ X31 )
      | ( X32 != X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('61',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( v1_subset_1 @ X31 @ X31 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X31: $i] :
      ~ ( v1_subset_1 @ X31 @ X31 ) ),
    inference(demod,[status(thm)],['61','65'])).

thf('67',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['57'])).

thf('69',plain,(
    ! [X17: $i] :
      ( ( ( k3_yellow_0 @ X17 )
        = ( k1_yellow_0 @ X17 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32 = X31 )
      | ( v1_subset_1 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('72',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['69','78'])).

thf('80',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('82',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('83',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['57'])).

thf('87',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','67','68','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X5VexINtTq
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.75  % Solved by: fo/fo7.sh
% 0.53/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.75  % done 482 iterations in 0.291s
% 0.53/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.75  % SZS output start Refutation
% 0.53/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.75  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.53/0.75  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.53/0.75  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.53/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.75  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.53/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.75  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.53/0.75  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.53/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.75  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.53/0.75  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.53/0.75  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.53/0.75  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.53/0.75  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.53/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.75  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.53/0.75  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.53/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.75  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.53/0.75  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.53/0.75  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.53/0.75  thf(t8_waybel_7, conjecture,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.53/0.75         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.53/0.75         ( l1_orders_2 @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.53/0.75             ( v13_waybel_0 @ B @ A ) & 
% 0.53/0.75             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.75           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.53/0.75             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.53/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.75    (~( ![A:$i]:
% 0.53/0.75        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.53/0.75            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.53/0.75            ( l1_orders_2 @ A ) ) =>
% 0.53/0.75          ( ![B:$i]:
% 0.53/0.75            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.53/0.75                ( v13_waybel_0 @ B @ A ) & 
% 0.53/0.75                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.75              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.53/0.75                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.53/0.75    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.53/0.75  thf('0', plain,
% 0.53/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.53/0.75        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('1', plain,
% 0.53/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.53/0.75       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('split', [status(esa)], ['0'])).
% 0.53/0.75  thf(d3_tarski, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( r1_tarski @ A @ B ) <=>
% 0.53/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.53/0.75  thf('2', plain,
% 0.53/0.75      (![X1 : $i, X3 : $i]:
% 0.53/0.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.75  thf(t1_subset, axiom,
% 0.53/0.75    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.53/0.75  thf('3', plain,
% 0.53/0.75      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.53/0.75      inference('cnf', [status(esa)], [t1_subset])).
% 0.53/0.75  thf('4', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r1_tarski @ X0 @ X1) | (m1_subset_1 @ (sk_C @ X1 @ X0) @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.75  thf(d11_yellow_0, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( l1_orders_2 @ A ) =>
% 0.53/0.75       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.53/0.75  thf('5', plain,
% 0.53/0.75      (![X17 : $i]:
% 0.53/0.75         (((k3_yellow_0 @ X17) = (k1_yellow_0 @ X17 @ k1_xboole_0))
% 0.53/0.75          | ~ (l1_orders_2 @ X17))),
% 0.53/0.75      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.53/0.75  thf(t42_yellow_0, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.53/0.75         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.53/0.75       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 0.53/0.75         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 0.53/0.75  thf('6', plain,
% 0.53/0.75      (![X24 : $i]:
% 0.53/0.75         ((r1_yellow_0 @ X24 @ k1_xboole_0)
% 0.53/0.75          | ~ (l1_orders_2 @ X24)
% 0.53/0.75          | ~ (v1_yellow_0 @ X24)
% 0.53/0.75          | ~ (v5_orders_2 @ X24)
% 0.53/0.75          | (v2_struct_0 @ X24))),
% 0.53/0.75      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.53/0.75  thf('7', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r1_tarski @ X0 @ X1) | (m1_subset_1 @ (sk_C @ X1 @ X0) @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.75  thf(t6_yellow_0, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( l1_orders_2 @ A ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.53/0.75             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.53/0.75  thf('8', plain,
% 0.53/0.75      (![X25 : $i, X26 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 0.53/0.75          | (r2_lattice3 @ X26 @ k1_xboole_0 @ X25)
% 0.53/0.75          | ~ (l1_orders_2 @ X26))),
% 0.53/0.75      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.53/0.75  thf('9', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r1_tarski @ (u1_struct_0 @ X0) @ X1)
% 0.53/0.75          | ~ (l1_orders_2 @ X0)
% 0.53/0.75          | (r2_lattice3 @ X0 @ k1_xboole_0 @ (sk_C @ X1 @ (u1_struct_0 @ X0))))),
% 0.53/0.75      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.75  thf('10', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r1_tarski @ X0 @ X1) | (m1_subset_1 @ (sk_C @ X1 @ X0) @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.75  thf(dt_k1_yellow_0, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( l1_orders_2 @ A ) =>
% 0.53/0.75       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.53/0.75  thf('11', plain,
% 0.53/0.75      (![X22 : $i, X23 : $i]:
% 0.53/0.75         (~ (l1_orders_2 @ X22)
% 0.53/0.75          | (m1_subset_1 @ (k1_yellow_0 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.53/0.75  thf(d9_yellow_0, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( l1_orders_2 @ A ) =>
% 0.53/0.75       ( ![B:$i,C:$i]:
% 0.53/0.75         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75           ( ( r1_yellow_0 @ A @ B ) =>
% 0.53/0.75             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 0.53/0.75               ( ( r2_lattice3 @ A @ B @ C ) & 
% 0.53/0.75                 ( ![D:$i]:
% 0.53/0.75                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 0.53/0.75                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf('12', plain,
% 0.53/0.75      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.53/0.75         (((X20) != (k1_yellow_0 @ X18 @ X19))
% 0.53/0.75          | ~ (r2_lattice3 @ X18 @ X19 @ X21)
% 0.53/0.75          | (r1_orders_2 @ X18 @ X20 @ X21)
% 0.53/0.75          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.53/0.75          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.53/0.75          | ~ (r1_yellow_0 @ X18 @ X19)
% 0.53/0.75          | ~ (l1_orders_2 @ X18))),
% 0.53/0.75      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.53/0.75  thf('13', plain,
% 0.53/0.75      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.53/0.75         (~ (l1_orders_2 @ X18)
% 0.53/0.75          | ~ (r1_yellow_0 @ X18 @ X19)
% 0.53/0.75          | ~ (m1_subset_1 @ (k1_yellow_0 @ X18 @ X19) @ (u1_struct_0 @ X18))
% 0.53/0.75          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.53/0.75          | (r1_orders_2 @ X18 @ (k1_yellow_0 @ X18 @ X19) @ X21)
% 0.53/0.75          | ~ (r2_lattice3 @ X18 @ X19 @ X21))),
% 0.53/0.75      inference('simplify', [status(thm)], ['12'])).
% 0.53/0.75  thf('14', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         (~ (l1_orders_2 @ X0)
% 0.53/0.75          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.53/0.75          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.53/0.75          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.53/0.75          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.53/0.75          | ~ (l1_orders_2 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['11', '13'])).
% 0.53/0.75  thf('15', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         (~ (r1_yellow_0 @ X0 @ X1)
% 0.53/0.75          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.53/0.75          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.53/0.75          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.53/0.75          | ~ (l1_orders_2 @ X0))),
% 0.53/0.75      inference('simplify', [status(thm)], ['14'])).
% 0.53/0.75  thf('16', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         ((r1_tarski @ (u1_struct_0 @ X0) @ X1)
% 0.53/0.75          | ~ (l1_orders_2 @ X0)
% 0.53/0.75          | ~ (r2_lattice3 @ X0 @ X2 @ (sk_C @ X1 @ (u1_struct_0 @ X0)))
% 0.53/0.75          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.53/0.75             (sk_C @ X1 @ (u1_struct_0 @ X0)))
% 0.53/0.75          | ~ (r1_yellow_0 @ X0 @ X2))),
% 0.53/0.75      inference('sup-', [status(thm)], ['10', '15'])).
% 0.53/0.75  thf('17', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (l1_orders_2 @ X0)
% 0.53/0.75          | (r1_tarski @ (u1_struct_0 @ X0) @ X1)
% 0.53/0.75          | ~ (r1_yellow_0 @ X0 @ k1_xboole_0)
% 0.53/0.75          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.53/0.75             (sk_C @ X1 @ (u1_struct_0 @ X0)))
% 0.53/0.75          | ~ (l1_orders_2 @ X0)
% 0.53/0.75          | (r1_tarski @ (u1_struct_0 @ X0) @ X1))),
% 0.53/0.75      inference('sup-', [status(thm)], ['9', '16'])).
% 0.53/0.75  thf('18', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.53/0.75           (sk_C @ X1 @ (u1_struct_0 @ X0)))
% 0.53/0.75          | ~ (r1_yellow_0 @ X0 @ k1_xboole_0)
% 0.53/0.75          | (r1_tarski @ (u1_struct_0 @ X0) @ X1)
% 0.53/0.75          | ~ (l1_orders_2 @ X0))),
% 0.53/0.75      inference('simplify', [status(thm)], ['17'])).
% 0.53/0.75  thf('19', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X0)
% 0.53/0.75          | ~ (v5_orders_2 @ X0)
% 0.53/0.75          | ~ (v1_yellow_0 @ X0)
% 0.53/0.75          | ~ (l1_orders_2 @ X0)
% 0.53/0.75          | ~ (l1_orders_2 @ X0)
% 0.53/0.75          | (r1_tarski @ (u1_struct_0 @ X0) @ X1)
% 0.53/0.75          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.53/0.75             (sk_C @ X1 @ (u1_struct_0 @ X0))))),
% 0.53/0.75      inference('sup-', [status(thm)], ['6', '18'])).
% 0.53/0.75  thf('20', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.53/0.75           (sk_C @ X1 @ (u1_struct_0 @ X0)))
% 0.53/0.75          | (r1_tarski @ (u1_struct_0 @ X0) @ X1)
% 0.53/0.75          | ~ (l1_orders_2 @ X0)
% 0.53/0.75          | ~ (v1_yellow_0 @ X0)
% 0.53/0.75          | ~ (v5_orders_2 @ X0)
% 0.53/0.75          | (v2_struct_0 @ X0))),
% 0.53/0.75      inference('simplify', [status(thm)], ['19'])).
% 0.53/0.75  thf('21', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 0.53/0.75           (sk_C @ X1 @ (u1_struct_0 @ X0)))
% 0.53/0.75          | ~ (l1_orders_2 @ X0)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (v5_orders_2 @ X0)
% 0.53/0.75          | ~ (v1_yellow_0 @ X0)
% 0.53/0.75          | ~ (l1_orders_2 @ X0)
% 0.53/0.75          | (r1_tarski @ (u1_struct_0 @ X0) @ X1))),
% 0.53/0.75      inference('sup+', [status(thm)], ['5', '20'])).
% 0.53/0.75  thf('22', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r1_tarski @ (u1_struct_0 @ X0) @ X1)
% 0.53/0.75          | ~ (v1_yellow_0 @ X0)
% 0.53/0.75          | ~ (v5_orders_2 @ X0)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (l1_orders_2 @ X0)
% 0.53/0.75          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ 
% 0.53/0.75             (sk_C @ X1 @ (u1_struct_0 @ X0))))),
% 0.53/0.75      inference('simplify', [status(thm)], ['21'])).
% 0.53/0.75  thf('23', plain,
% 0.53/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.53/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('split', [status(esa)], ['0'])).
% 0.53/0.75  thf('24', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(t3_subset, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.75  thf('25', plain,
% 0.53/0.75      (![X11 : $i, X12 : $i]:
% 0.53/0.75         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.75  thf('26', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['24', '25'])).
% 0.53/0.75  thf('27', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X0 @ X1)
% 0.53/0.75          | (r2_hidden @ X0 @ X2)
% 0.53/0.75          | ~ (r1_tarski @ X1 @ X2))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.75  thf('28', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.53/0.75      inference('sup-', [status(thm)], ['26', '27'])).
% 0.53/0.75  thf('29', plain,
% 0.53/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.53/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['23', '28'])).
% 0.53/0.75  thf('30', plain,
% 0.53/0.75      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.53/0.75      inference('cnf', [status(esa)], [t1_subset])).
% 0.53/0.75  thf('31', plain,
% 0.53/0.75      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.53/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.75  thf('32', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(d20_waybel_0, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( l1_orders_2 @ A ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.75           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.53/0.75             ( ![C:$i]:
% 0.53/0.75               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75                 ( ![D:$i]:
% 0.53/0.75                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.53/0.75                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf('33', plain,
% 0.53/0.75      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.53/0.75          | ~ (v13_waybel_0 @ X27 @ X28)
% 0.53/0.75          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.53/0.75          | (r2_hidden @ X29 @ X27)
% 0.53/0.75          | ~ (r1_orders_2 @ X28 @ X30 @ X29)
% 0.53/0.75          | ~ (r2_hidden @ X30 @ X27)
% 0.53/0.75          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.53/0.75          | ~ (l1_orders_2 @ X28))),
% 0.53/0.75      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.53/0.75  thf('34', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (l1_orders_2 @ sk_A)
% 0.53/0.75          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.75          | ~ (r2_hidden @ X0 @ sk_B)
% 0.53/0.75          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.53/0.75          | (r2_hidden @ X1 @ sk_B)
% 0.53/0.75          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.53/0.75          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['32', '33'])).
% 0.53/0.75  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('36', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('37', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.75          | ~ (r2_hidden @ X0 @ sk_B)
% 0.53/0.75          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.53/0.75          | (r2_hidden @ X1 @ sk_B)
% 0.53/0.75          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.53/0.75  thf('38', plain,
% 0.53/0.75      ((![X0 : $i]:
% 0.53/0.75          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.75           | (r2_hidden @ X0 @ sk_B)
% 0.53/0.75           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.53/0.75           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.53/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['31', '37'])).
% 0.53/0.75  thf('39', plain,
% 0.53/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.53/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('split', [status(esa)], ['0'])).
% 0.53/0.75  thf('40', plain,
% 0.53/0.75      ((![X0 : $i]:
% 0.53/0.75          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.75           | (r2_hidden @ X0 @ sk_B)
% 0.53/0.75           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.53/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('demod', [status(thm)], ['38', '39'])).
% 0.53/0.75  thf('41', plain,
% 0.53/0.75      ((![X0 : $i]:
% 0.53/0.75          (~ (l1_orders_2 @ sk_A)
% 0.53/0.75           | (v2_struct_0 @ sk_A)
% 0.53/0.75           | ~ (v5_orders_2 @ sk_A)
% 0.53/0.75           | ~ (v1_yellow_0 @ sk_A)
% 0.53/0.75           | (r1_tarski @ (u1_struct_0 @ sk_A) @ X0)
% 0.53/0.75           | (r2_hidden @ (sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.53/0.75           | ~ (m1_subset_1 @ (sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 0.53/0.75                (u1_struct_0 @ sk_A))))
% 0.53/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['22', '40'])).
% 0.53/0.75  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('43', plain, ((v5_orders_2 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('44', plain, ((v1_yellow_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('45', plain,
% 0.53/0.75      ((![X0 : $i]:
% 0.53/0.75          ((v2_struct_0 @ sk_A)
% 0.53/0.75           | (r1_tarski @ (u1_struct_0 @ sk_A) @ X0)
% 0.53/0.75           | (r2_hidden @ (sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.53/0.75           | ~ (m1_subset_1 @ (sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 0.53/0.75                (u1_struct_0 @ sk_A))))
% 0.53/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.53/0.75  thf('46', plain,
% 0.53/0.75      ((![X0 : $i]:
% 0.53/0.75          ((r1_tarski @ (u1_struct_0 @ sk_A) @ X0)
% 0.53/0.75           | (r2_hidden @ (sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.53/0.75           | (r1_tarski @ (u1_struct_0 @ sk_A) @ X0)
% 0.53/0.75           | (v2_struct_0 @ sk_A)))
% 0.53/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['4', '45'])).
% 0.53/0.75  thf('47', plain,
% 0.53/0.75      ((![X0 : $i]:
% 0.53/0.75          ((v2_struct_0 @ sk_A)
% 0.53/0.75           | (r2_hidden @ (sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.53/0.75           | (r1_tarski @ (u1_struct_0 @ sk_A) @ X0)))
% 0.53/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['46'])).
% 0.53/0.75  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('49', plain,
% 0.53/0.75      ((![X0 : $i]:
% 0.53/0.75          ((r1_tarski @ (u1_struct_0 @ sk_A) @ X0)
% 0.53/0.75           | (r2_hidden @ (sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B)))
% 0.53/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('clc', [status(thm)], ['47', '48'])).
% 0.53/0.75  thf('50', plain,
% 0.53/0.75      (![X1 : $i, X3 : $i]:
% 0.53/0.75         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.75  thf('51', plain,
% 0.53/0.75      ((((r1_tarski @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.53/0.75         | (r1_tarski @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.53/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['49', '50'])).
% 0.53/0.75  thf('52', plain,
% 0.53/0.75      (((r1_tarski @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.53/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['51'])).
% 0.53/0.75  thf('53', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['24', '25'])).
% 0.53/0.75  thf(d10_xboole_0, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.75  thf('54', plain,
% 0.53/0.75      (![X4 : $i, X6 : $i]:
% 0.53/0.75         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.53/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.75  thf('55', plain,
% 0.53/0.75      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.53/0.75        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.53/0.75  thf('56', plain,
% 0.53/0.75      ((((u1_struct_0 @ sk_A) = (sk_B)))
% 0.53/0.75         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['52', '55'])).
% 0.53/0.75  thf('57', plain,
% 0.53/0.75      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.53/0.75        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('58', plain,
% 0.53/0.75      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.53/0.75         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.53/0.75      inference('split', [status(esa)], ['57'])).
% 0.53/0.75  thf('59', plain,
% 0.53/0.75      (((v1_subset_1 @ sk_B @ sk_B))
% 0.53/0.75         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.53/0.75             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('sup+', [status(thm)], ['56', '58'])).
% 0.53/0.75  thf(d7_subset_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.75       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.53/0.75  thf('60', plain,
% 0.53/0.75      (![X31 : $i, X32 : $i]:
% 0.53/0.75         (~ (v1_subset_1 @ X32 @ X31)
% 0.53/0.75          | ((X32) != (X31))
% 0.53/0.75          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.53/0.75  thf('61', plain,
% 0.53/0.75      (![X31 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X31))
% 0.53/0.75          | ~ (v1_subset_1 @ X31 @ X31))),
% 0.53/0.75      inference('simplify', [status(thm)], ['60'])).
% 0.53/0.75  thf('62', plain,
% 0.53/0.75      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.75  thf('63', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.53/0.75      inference('simplify', [status(thm)], ['62'])).
% 0.53/0.75  thf('64', plain,
% 0.53/0.75      (![X11 : $i, X13 : $i]:
% 0.53/0.75         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.53/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.75  thf('65', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['63', '64'])).
% 0.53/0.75  thf('66', plain, (![X31 : $i]: ~ (v1_subset_1 @ X31 @ X31)),
% 0.53/0.75      inference('demod', [status(thm)], ['61', '65'])).
% 0.53/0.75  thf('67', plain,
% 0.53/0.75      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.53/0.75       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['59', '66'])).
% 0.53/0.75  thf('68', plain,
% 0.53/0.75      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.53/0.75       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('split', [status(esa)], ['57'])).
% 0.53/0.75  thf('69', plain,
% 0.53/0.75      (![X17 : $i]:
% 0.53/0.75         (((k3_yellow_0 @ X17) = (k1_yellow_0 @ X17 @ k1_xboole_0))
% 0.53/0.75          | ~ (l1_orders_2 @ X17))),
% 0.53/0.75      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.53/0.75  thf('70', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('71', plain,
% 0.53/0.75      (![X31 : $i, X32 : $i]:
% 0.53/0.75         (((X32) = (X31))
% 0.53/0.75          | (v1_subset_1 @ X32 @ X31)
% 0.53/0.75          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.53/0.75  thf('72', plain,
% 0.53/0.75      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.53/0.75        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['70', '71'])).
% 0.53/0.75  thf('73', plain,
% 0.53/0.75      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.53/0.75         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.53/0.75      inference('split', [status(esa)], ['0'])).
% 0.53/0.75  thf('74', plain,
% 0.53/0.75      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.53/0.75         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.53/0.75      inference('sup-', [status(thm)], ['72', '73'])).
% 0.53/0.75  thf('75', plain,
% 0.53/0.75      (![X22 : $i, X23 : $i]:
% 0.53/0.75         (~ (l1_orders_2 @ X22)
% 0.53/0.75          | (m1_subset_1 @ (k1_yellow_0 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.53/0.75  thf('76', plain,
% 0.53/0.75      ((![X0 : $i]:
% 0.53/0.75          ((m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ sk_B)
% 0.53/0.75           | ~ (l1_orders_2 @ sk_A)))
% 0.53/0.75         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.53/0.75      inference('sup+', [status(thm)], ['74', '75'])).
% 0.53/0.75  thf('77', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('78', plain,
% 0.53/0.75      ((![X0 : $i]: (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ sk_B))
% 0.53/0.75         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.53/0.75      inference('demod', [status(thm)], ['76', '77'])).
% 0.53/0.75  thf('79', plain,
% 0.53/0.75      ((((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B) | ~ (l1_orders_2 @ sk_A)))
% 0.53/0.75         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.53/0.75      inference('sup+', [status(thm)], ['69', '78'])).
% 0.53/0.75  thf('80', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('81', plain,
% 0.53/0.75      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.53/0.75         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.53/0.75      inference('demod', [status(thm)], ['79', '80'])).
% 0.53/0.75  thf(t2_subset, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( m1_subset_1 @ A @ B ) =>
% 0.53/0.75       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.53/0.75  thf('82', plain,
% 0.53/0.75      (![X9 : $i, X10 : $i]:
% 0.53/0.75         ((r2_hidden @ X9 @ X10)
% 0.53/0.75          | (v1_xboole_0 @ X10)
% 0.53/0.75          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.53/0.75      inference('cnf', [status(esa)], [t2_subset])).
% 0.53/0.75  thf('83', plain,
% 0.53/0.75      ((((v1_xboole_0 @ sk_B) | (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.53/0.75         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.53/0.75      inference('sup-', [status(thm)], ['81', '82'])).
% 0.53/0.75  thf('84', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('85', plain,
% 0.53/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.53/0.75         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.53/0.75      inference('clc', [status(thm)], ['83', '84'])).
% 0.53/0.75  thf('86', plain,
% 0.53/0.75      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.53/0.75         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('split', [status(esa)], ['57'])).
% 0.53/0.75  thf('87', plain,
% 0.53/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.53/0.75       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['85', '86'])).
% 0.53/0.75  thf('88', plain, ($false),
% 0.53/0.75      inference('sat_resolution*', [status(thm)], ['1', '67', '68', '87'])).
% 0.53/0.75  
% 0.53/0.75  % SZS output end Refutation
% 0.53/0.75  
% 0.53/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
