%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.stL3jzS28S

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:10 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 481 expanded)
%              Number of leaves         :   40 ( 151 expanded)
%              Depth                    :   26
%              Number of atoms          : 1676 (7231 expanded)
%              Number of equality atoms :   38 (  95 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

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

thf(t42_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( r1_yellow_0 @ A @ k1_xboole_0 )
        & ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X24: $i] :
      ( ( r1_yellow_0 @ X24 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v1_yellow_0 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( X8 = X6 )
      | ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( X8 = X6 )
      | ~ ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(t6_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( r2_lattice3 @ X26 @ k1_xboole_0 @ X25 )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('26',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('30',plain,(
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

thf('31',plain,(
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

thf('32',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ( r1_orders_2 @ X18 @ ( k1_yellow_0 @ X18 @ X19 ) @ X21 )
      | ~ ( r2_lattice3 @ X18 @ X19 @ X21 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','39'])).

thf('41',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('48',plain,(
    ! [X17: $i] :
      ( ( ( k3_yellow_0 @ X17 )
        = ( k1_yellow_0 @ X17 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('49',plain,(
    ! [X24: $i] :
      ( ( r1_yellow_0 @ X24 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v1_yellow_0 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('51',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( r2_lattice3 @ X26 @ k1_xboole_0 @ X25 )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t6_yellow_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('66',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
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

thf('70',plain,(
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

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','77'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','84'])).

thf('86',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('93',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
        | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('95',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['46','95'])).

thf('97',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','18'])).

thf('98',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('100',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['101'])).

thf('103',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['100','102'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('104',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_subset_1 @ X32 @ X31 )
      | ( X32 != X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('105',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( v1_subset_1 @ X31 @ X31 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('107',plain,(
    ! [X31: $i] :
      ~ ( v1_subset_1 @ X31 @ X31 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','107'])).

thf('109',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['101'])).

thf('110',plain,(
    ! [X17: $i] :
      ( ( ( k3_yellow_0 @ X17 )
        = ( k1_yellow_0 @ X17 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('111',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32 = X31 )
      | ( v1_subset_1 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('113',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('115',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['110','119'])).

thf('121',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('123',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('124',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['101'])).

thf('128',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','108','109','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.stL3jzS28S
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:23:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.75  % Solved by: fo/fo7.sh
% 0.52/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.75  % done 482 iterations in 0.299s
% 0.52/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.75  % SZS output start Refutation
% 0.52/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.75  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.52/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.75  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.52/0.75  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.52/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.75  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.52/0.75  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.52/0.75  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.52/0.75  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 0.52/0.75  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.52/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.75  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.52/0.75  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.52/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.75  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.52/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.75  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.52/0.75  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.52/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.75  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.52/0.75  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.52/0.75  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.52/0.75  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.52/0.75  thf(t8_waybel_7, conjecture,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.52/0.75         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.52/0.75         ( l1_orders_2 @ A ) ) =>
% 0.52/0.75       ( ![B:$i]:
% 0.52/0.75         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.52/0.75             ( v13_waybel_0 @ B @ A ) & 
% 0.52/0.75             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.52/0.75           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.52/0.75             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.52/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.75    (~( ![A:$i]:
% 0.52/0.75        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.52/0.75            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.52/0.75            ( l1_orders_2 @ A ) ) =>
% 0.52/0.75          ( ![B:$i]:
% 0.52/0.75            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.52/0.75                ( v13_waybel_0 @ B @ A ) & 
% 0.52/0.75                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.52/0.75              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.52/0.75                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.52/0.75    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.52/0.75  thf('0', plain,
% 0.52/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.52/0.75        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('1', plain,
% 0.52/0.75      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.52/0.75       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.52/0.75      inference('split', [status(esa)], ['0'])).
% 0.52/0.75  thf(t42_yellow_0, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.52/0.75         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.52/0.75       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 0.52/0.75         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 0.52/0.75  thf('2', plain,
% 0.52/0.75      (![X24 : $i]:
% 0.52/0.75         ((r1_yellow_0 @ X24 @ k1_xboole_0)
% 0.52/0.75          | ~ (l1_orders_2 @ X24)
% 0.52/0.75          | ~ (v1_yellow_0 @ X24)
% 0.52/0.75          | ~ (v5_orders_2 @ X24)
% 0.52/0.75          | (v2_struct_0 @ X24))),
% 0.52/0.75      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.52/0.75  thf('3', plain,
% 0.52/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf(d10_xboole_0, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.75  thf('4', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.52/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.75  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.52/0.76      inference('simplify', [status(thm)], ['4'])).
% 0.52/0.76  thf(t3_subset, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.76  thf('6', plain,
% 0.52/0.76      (![X11 : $i, X13 : $i]:
% 0.52/0.76         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.52/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.76  thf('7', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.76  thf(t8_subset_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.76       ( ![C:$i]:
% 0.52/0.76         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.76           ( ( ![D:$i]:
% 0.52/0.76               ( ( m1_subset_1 @ D @ A ) =>
% 0.52/0.76                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.52/0.76             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.52/0.76  thf('8', plain,
% 0.52/0.76      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.52/0.76          | ((X8) = (X6))
% 0.52/0.76          | (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X8)
% 0.52/0.76          | (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X6)
% 0.52/0.76          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.52/0.76  thf('9', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.76          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.52/0.76          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.52/0.76          | ((X1) = (X0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.52/0.76  thf('10', plain,
% 0.52/0.76      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.52/0.76        | (r2_hidden @ 
% 0.52/0.76           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.52/0.76        | (r2_hidden @ 
% 0.52/0.76           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.52/0.76           (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['3', '9'])).
% 0.52/0.76  thf('11', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('12', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.76  thf('13', plain,
% 0.52/0.76      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.52/0.76          | ((X8) = (X6))
% 0.52/0.76          | ~ (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X8)
% 0.52/0.76          | ~ (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X6)
% 0.52/0.76          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.52/0.76  thf('14', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.76          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.52/0.76          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.52/0.76          | ((X1) = (X0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['12', '13'])).
% 0.52/0.76  thf('15', plain,
% 0.52/0.76      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.52/0.76        | ~ (r2_hidden @ 
% 0.52/0.76             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.52/0.76        | ~ (r2_hidden @ 
% 0.52/0.76             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.52/0.76             (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['11', '14'])).
% 0.52/0.76  thf('16', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(l3_subset_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.76       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.52/0.76  thf('17', plain,
% 0.52/0.76      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X3 @ X4)
% 0.52/0.76          | (r2_hidden @ X3 @ X5)
% 0.52/0.76          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.52/0.76      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.52/0.76  thf('18', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.52/0.76      inference('sup-', [status(thm)], ['16', '17'])).
% 0.52/0.76  thf('19', plain,
% 0.52/0.76      ((~ (r2_hidden @ 
% 0.52/0.76           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.52/0.76        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('clc', [status(thm)], ['15', '18'])).
% 0.52/0.76  thf('20', plain,
% 0.52/0.76      (((r2_hidden @ 
% 0.52/0.76         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.52/0.76         (u1_struct_0 @ sk_A))
% 0.52/0.76        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('clc', [status(thm)], ['10', '19'])).
% 0.52/0.76  thf('21', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.76  thf(t4_subset, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.52/0.76       ( m1_subset_1 @ A @ C ) ))).
% 0.52/0.76  thf('22', plain,
% 0.52/0.76      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X14 @ X15)
% 0.52/0.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.52/0.76          | (m1_subset_1 @ X14 @ X16))),
% 0.52/0.76      inference('cnf', [status(esa)], [t4_subset])).
% 0.52/0.76  thf('23', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.76  thf('24', plain,
% 0.52/0.76      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.52/0.76        | (m1_subset_1 @ 
% 0.52/0.76           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.52/0.76           (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['20', '23'])).
% 0.52/0.76  thf(t6_yellow_0, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ( l1_orders_2 @ A ) =>
% 0.52/0.76       ( ![B:$i]:
% 0.52/0.76         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.52/0.76           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.52/0.76             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.52/0.76  thf('25', plain,
% 0.52/0.76      (![X25 : $i, X26 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 0.52/0.76          | (r2_lattice3 @ X26 @ k1_xboole_0 @ X25)
% 0.52/0.76          | ~ (l1_orders_2 @ X26))),
% 0.52/0.76      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.52/0.76  thf('26', plain,
% 0.52/0.76      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.52/0.76        | ~ (l1_orders_2 @ sk_A)
% 0.52/0.76        | (r2_lattice3 @ sk_A @ k1_xboole_0 @ 
% 0.52/0.76           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['24', '25'])).
% 0.52/0.76  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('28', plain,
% 0.52/0.76      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.52/0.76        | (r2_lattice3 @ sk_A @ k1_xboole_0 @ 
% 0.52/0.76           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('demod', [status(thm)], ['26', '27'])).
% 0.52/0.76  thf('29', plain,
% 0.52/0.76      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.52/0.76        | (m1_subset_1 @ 
% 0.52/0.76           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.52/0.76           (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['20', '23'])).
% 0.52/0.76  thf(dt_k1_yellow_0, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( l1_orders_2 @ A ) =>
% 0.52/0.76       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.52/0.76  thf('30', plain,
% 0.52/0.76      (![X22 : $i, X23 : $i]:
% 0.52/0.76         (~ (l1_orders_2 @ X22)
% 0.52/0.76          | (m1_subset_1 @ (k1_yellow_0 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.52/0.76  thf(d9_yellow_0, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ( l1_orders_2 @ A ) =>
% 0.52/0.76       ( ![B:$i,C:$i]:
% 0.52/0.76         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.52/0.76           ( ( r1_yellow_0 @ A @ B ) =>
% 0.52/0.76             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 0.52/0.76               ( ( r2_lattice3 @ A @ B @ C ) & 
% 0.52/0.76                 ( ![D:$i]:
% 0.52/0.76                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.52/0.76                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 0.52/0.76                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.76  thf('31', plain,
% 0.52/0.76      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.76         (((X20) != (k1_yellow_0 @ X18 @ X19))
% 0.52/0.76          | ~ (r2_lattice3 @ X18 @ X19 @ X21)
% 0.52/0.76          | (r1_orders_2 @ X18 @ X20 @ X21)
% 0.52/0.76          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.52/0.76          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.52/0.76          | ~ (r1_yellow_0 @ X18 @ X19)
% 0.52/0.76          | ~ (l1_orders_2 @ X18))),
% 0.52/0.76      inference('cnf', [status(esa)], [d9_yellow_0])).
% 0.52/0.76  thf('32', plain,
% 0.52/0.76      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.52/0.76         (~ (l1_orders_2 @ X18)
% 0.52/0.76          | ~ (r1_yellow_0 @ X18 @ X19)
% 0.52/0.76          | ~ (m1_subset_1 @ (k1_yellow_0 @ X18 @ X19) @ (u1_struct_0 @ X18))
% 0.52/0.76          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.52/0.76          | (r1_orders_2 @ X18 @ (k1_yellow_0 @ X18 @ X19) @ X21)
% 0.52/0.76          | ~ (r2_lattice3 @ X18 @ X19 @ X21))),
% 0.52/0.76      inference('simplify', [status(thm)], ['31'])).
% 0.52/0.76  thf('33', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         (~ (l1_orders_2 @ X0)
% 0.52/0.76          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.52/0.76          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.52/0.76          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.52/0.76          | ~ (r1_yellow_0 @ X0 @ X1)
% 0.52/0.76          | ~ (l1_orders_2 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['30', '32'])).
% 0.52/0.76  thf('34', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         (~ (r1_yellow_0 @ X0 @ X1)
% 0.52/0.76          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.52/0.76          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.52/0.76          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.52/0.76          | ~ (l1_orders_2 @ X0))),
% 0.52/0.76      inference('simplify', [status(thm)], ['33'])).
% 0.52/0.76  thf('35', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((sk_B) = (u1_struct_0 @ sk_A))
% 0.52/0.76          | ~ (l1_orders_2 @ sk_A)
% 0.52/0.76          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 0.52/0.76               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.52/0.76          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.52/0.76             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.52/0.76          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['29', '34'])).
% 0.52/0.76  thf('36', plain, ((l1_orders_2 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('37', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((sk_B) = (u1_struct_0 @ sk_A))
% 0.52/0.76          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 0.52/0.76               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.52/0.76          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 0.52/0.76             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.52/0.76          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 0.52/0.76      inference('demod', [status(thm)], ['35', '36'])).
% 0.52/0.76  thf('38', plain,
% 0.52/0.76      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.52/0.76        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 0.52/0.76        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.52/0.76           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.52/0.76        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['28', '37'])).
% 0.52/0.76  thf('39', plain,
% 0.52/0.76      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.52/0.76         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.52/0.76        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 0.52/0.76        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['38'])).
% 0.52/0.76  thf('40', plain,
% 0.52/0.76      (((v2_struct_0 @ sk_A)
% 0.52/0.76        | ~ (v5_orders_2 @ sk_A)
% 0.52/0.76        | ~ (v1_yellow_0 @ sk_A)
% 0.52/0.76        | ~ (l1_orders_2 @ sk_A)
% 0.52/0.76        | ((sk_B) = (u1_struct_0 @ sk_A))
% 0.52/0.76        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.52/0.76           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['2', '39'])).
% 0.52/0.76  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('42', plain, ((v1_yellow_0 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('44', plain,
% 0.52/0.76      (((v2_struct_0 @ sk_A)
% 0.52/0.76        | ((sk_B) = (u1_struct_0 @ sk_A))
% 0.52/0.76        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.52/0.76           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.52/0.76  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('46', plain,
% 0.52/0.76      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 0.52/0.76         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.52/0.76        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('clc', [status(thm)], ['44', '45'])).
% 0.52/0.76  thf('47', plain,
% 0.52/0.76      (![X22 : $i, X23 : $i]:
% 0.52/0.76         (~ (l1_orders_2 @ X22)
% 0.52/0.76          | (m1_subset_1 @ (k1_yellow_0 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.52/0.76  thf(d11_yellow_0, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ( l1_orders_2 @ A ) =>
% 0.52/0.76       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 0.52/0.76  thf('48', plain,
% 0.52/0.76      (![X17 : $i]:
% 0.52/0.76         (((k3_yellow_0 @ X17) = (k1_yellow_0 @ X17 @ k1_xboole_0))
% 0.52/0.76          | ~ (l1_orders_2 @ X17))),
% 0.52/0.76      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.52/0.76  thf('49', plain,
% 0.52/0.76      (![X24 : $i]:
% 0.52/0.76         ((r1_yellow_0 @ X24 @ k1_xboole_0)
% 0.52/0.76          | ~ (l1_orders_2 @ X24)
% 0.52/0.76          | ~ (v1_yellow_0 @ X24)
% 0.52/0.76          | ~ (v5_orders_2 @ X24)
% 0.52/0.76          | (v2_struct_0 @ X24))),
% 0.52/0.76      inference('cnf', [status(esa)], [t42_yellow_0])).
% 0.52/0.76  thf('50', plain,
% 0.52/0.76      (![X22 : $i, X23 : $i]:
% 0.52/0.76         (~ (l1_orders_2 @ X22)
% 0.52/0.76          | (m1_subset_1 @ (k1_yellow_0 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.52/0.76  thf('51', plain,
% 0.52/0.76      (![X25 : $i, X26 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 0.52/0.76          | (r2_lattice3 @ X26 @ k1_xboole_0 @ X25)
% 0.52/0.76          | ~ (l1_orders_2 @ X26))),
% 0.52/0.76      inference('cnf', [status(esa)], [t6_yellow_0])).
% 0.52/0.76  thf('52', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (~ (l1_orders_2 @ X0)
% 0.52/0.76          | ~ (l1_orders_2 @ X0)
% 0.52/0.76          | (r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ X1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['50', '51'])).
% 0.52/0.76  thf('53', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ X1))
% 0.52/0.76          | ~ (l1_orders_2 @ X0))),
% 0.52/0.76      inference('simplify', [status(thm)], ['52'])).
% 0.52/0.76  thf('54', plain,
% 0.52/0.76      (![X22 : $i, X23 : $i]:
% 0.52/0.76         (~ (l1_orders_2 @ X22)
% 0.52/0.76          | (m1_subset_1 @ (k1_yellow_0 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.52/0.76  thf('55', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         (~ (r1_yellow_0 @ X0 @ X1)
% 0.52/0.76          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.52/0.76          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 0.52/0.76          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 0.52/0.76          | ~ (l1_orders_2 @ X0))),
% 0.52/0.76      inference('simplify', [status(thm)], ['33'])).
% 0.52/0.76  thf('56', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         (~ (l1_orders_2 @ X0)
% 0.52/0.76          | ~ (l1_orders_2 @ X0)
% 0.52/0.76          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.52/0.76          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.52/0.76             (k1_yellow_0 @ X0 @ X1))
% 0.52/0.76          | ~ (r1_yellow_0 @ X0 @ X2))),
% 0.52/0.76      inference('sup-', [status(thm)], ['54', '55'])).
% 0.52/0.76  thf('57', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         (~ (r1_yellow_0 @ X0 @ X2)
% 0.52/0.76          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 0.52/0.76             (k1_yellow_0 @ X0 @ X1))
% 0.52/0.76          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 0.52/0.76          | ~ (l1_orders_2 @ X0))),
% 0.52/0.76      inference('simplify', [status(thm)], ['56'])).
% 0.52/0.76  thf('58', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (~ (l1_orders_2 @ X1)
% 0.52/0.76          | ~ (l1_orders_2 @ X1)
% 0.52/0.76          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 0.52/0.76             (k1_yellow_0 @ X1 @ X0))
% 0.52/0.76          | ~ (r1_yellow_0 @ X1 @ k1_xboole_0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['53', '57'])).
% 0.52/0.76  thf('59', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (~ (r1_yellow_0 @ X1 @ k1_xboole_0)
% 0.52/0.76          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 0.52/0.76             (k1_yellow_0 @ X1 @ X0))
% 0.52/0.76          | ~ (l1_orders_2 @ X1))),
% 0.52/0.76      inference('simplify', [status(thm)], ['58'])).
% 0.52/0.76  thf('60', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((v2_struct_0 @ X0)
% 0.52/0.76          | ~ (v5_orders_2 @ X0)
% 0.52/0.76          | ~ (v1_yellow_0 @ X0)
% 0.52/0.76          | ~ (l1_orders_2 @ X0)
% 0.52/0.76          | ~ (l1_orders_2 @ X0)
% 0.52/0.76          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.52/0.76             (k1_yellow_0 @ X0 @ X1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['49', '59'])).
% 0.52/0.76  thf('61', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 0.52/0.76           (k1_yellow_0 @ X0 @ X1))
% 0.52/0.76          | ~ (l1_orders_2 @ X0)
% 0.52/0.76          | ~ (v1_yellow_0 @ X0)
% 0.52/0.76          | ~ (v5_orders_2 @ X0)
% 0.52/0.76          | (v2_struct_0 @ X0))),
% 0.52/0.76      inference('simplify', [status(thm)], ['60'])).
% 0.52/0.76  thf('62', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 0.52/0.76          | ~ (l1_orders_2 @ X0)
% 0.52/0.76          | (v2_struct_0 @ X0)
% 0.52/0.76          | ~ (v5_orders_2 @ X0)
% 0.52/0.76          | ~ (v1_yellow_0 @ X0)
% 0.52/0.76          | ~ (l1_orders_2 @ X0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['48', '61'])).
% 0.52/0.76  thf('63', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (~ (v1_yellow_0 @ X0)
% 0.52/0.76          | ~ (v5_orders_2 @ X0)
% 0.52/0.76          | (v2_struct_0 @ X0)
% 0.52/0.76          | ~ (l1_orders_2 @ X0)
% 0.52/0.76          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['62'])).
% 0.52/0.76  thf('64', plain,
% 0.52/0.76      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('split', [status(esa)], ['0'])).
% 0.52/0.76  thf('65', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.52/0.76      inference('sup-', [status(thm)], ['16', '17'])).
% 0.52/0.76  thf('66', plain,
% 0.52/0.76      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['64', '65'])).
% 0.52/0.76  thf('67', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.76  thf('68', plain,
% 0.52/0.76      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['66', '67'])).
% 0.52/0.76  thf('69', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(d20_waybel_0, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ( l1_orders_2 @ A ) =>
% 0.52/0.76       ( ![B:$i]:
% 0.52/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.76           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.52/0.76             ( ![C:$i]:
% 0.52/0.76               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.52/0.76                 ( ![D:$i]:
% 0.52/0.76                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.52/0.76                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.52/0.76                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.76  thf('70', plain,
% 0.52/0.76      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.52/0.76          | ~ (v13_waybel_0 @ X27 @ X28)
% 0.52/0.76          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.52/0.76          | (r2_hidden @ X29 @ X27)
% 0.52/0.76          | ~ (r1_orders_2 @ X28 @ X30 @ X29)
% 0.52/0.76          | ~ (r2_hidden @ X30 @ X27)
% 0.52/0.76          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.52/0.76          | ~ (l1_orders_2 @ X28))),
% 0.52/0.76      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.52/0.76  thf('71', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (~ (l1_orders_2 @ sk_A)
% 0.52/0.76          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.52/0.76          | ~ (r2_hidden @ X0 @ sk_B)
% 0.52/0.76          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.52/0.76          | (r2_hidden @ X1 @ sk_B)
% 0.52/0.76          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.52/0.76          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 0.52/0.76      inference('sup-', [status(thm)], ['69', '70'])).
% 0.52/0.76  thf('72', plain, ((l1_orders_2 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('73', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('74', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.52/0.76          | ~ (r2_hidden @ X0 @ sk_B)
% 0.52/0.76          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.52/0.76          | (r2_hidden @ X1 @ sk_B)
% 0.52/0.76          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.52/0.76  thf('75', plain,
% 0.52/0.76      ((![X0 : $i]:
% 0.52/0.76          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.52/0.76           | (r2_hidden @ X0 @ sk_B)
% 0.52/0.76           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.52/0.76           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['68', '74'])).
% 0.52/0.76  thf('76', plain,
% 0.52/0.76      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('split', [status(esa)], ['0'])).
% 0.52/0.76  thf('77', plain,
% 0.52/0.76      ((![X0 : $i]:
% 0.52/0.76          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.52/0.76           | (r2_hidden @ X0 @ sk_B)
% 0.52/0.76           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('demod', [status(thm)], ['75', '76'])).
% 0.52/0.76  thf('78', plain,
% 0.52/0.76      ((![X0 : $i]:
% 0.52/0.76          (~ (l1_orders_2 @ sk_A)
% 0.52/0.76           | (v2_struct_0 @ sk_A)
% 0.52/0.76           | ~ (v5_orders_2 @ sk_A)
% 0.52/0.76           | ~ (v1_yellow_0 @ sk_A)
% 0.52/0.76           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B)
% 0.52/0.76           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['63', '77'])).
% 0.52/0.76  thf('79', plain, ((l1_orders_2 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('80', plain, ((v5_orders_2 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('81', plain, ((v1_yellow_0 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('82', plain,
% 0.52/0.76      ((![X0 : $i]:
% 0.52/0.76          ((v2_struct_0 @ sk_A)
% 0.52/0.76           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B)
% 0.52/0.76           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.52/0.76  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('84', plain,
% 0.52/0.76      ((![X0 : $i]:
% 0.52/0.76          (~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 0.52/0.76           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B)))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('clc', [status(thm)], ['82', '83'])).
% 0.52/0.76  thf('85', plain,
% 0.52/0.76      ((![X0 : $i]:
% 0.52/0.76          (~ (l1_orders_2 @ sk_A)
% 0.52/0.76           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B)))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['47', '84'])).
% 0.52/0.76  thf('86', plain, ((l1_orders_2 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('87', plain,
% 0.52/0.76      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('demod', [status(thm)], ['85', '86'])).
% 0.52/0.76  thf('88', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('89', plain,
% 0.52/0.76      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X14 @ X15)
% 0.52/0.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.52/0.76          | (m1_subset_1 @ X14 @ X16))),
% 0.52/0.76      inference('cnf', [status(esa)], [t4_subset])).
% 0.52/0.76  thf('90', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.52/0.76      inference('sup-', [status(thm)], ['88', '89'])).
% 0.52/0.76  thf('91', plain,
% 0.52/0.76      ((![X0 : $i]:
% 0.52/0.76          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['87', '90'])).
% 0.52/0.76  thf('92', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.52/0.76          | ~ (r2_hidden @ X0 @ sk_B)
% 0.52/0.76          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.52/0.76          | (r2_hidden @ X1 @ sk_B)
% 0.52/0.76          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.52/0.76  thf('93', plain,
% 0.52/0.76      ((![X0 : $i, X1 : $i]:
% 0.52/0.76          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.52/0.76           | (r2_hidden @ X1 @ sk_B)
% 0.52/0.76           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 0.52/0.76           | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B)))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['91', '92'])).
% 0.52/0.76  thf('94', plain,
% 0.52/0.76      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('demod', [status(thm)], ['85', '86'])).
% 0.52/0.76  thf('95', plain,
% 0.52/0.76      ((![X0 : $i, X1 : $i]:
% 0.52/0.76          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.52/0.76           | (r2_hidden @ X1 @ sk_B)
% 0.52/0.76           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('demod', [status(thm)], ['93', '94'])).
% 0.52/0.76  thf('96', plain,
% 0.52/0.76      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.52/0.76         | (r2_hidden @ 
% 0.52/0.76            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.52/0.76         | ~ (m1_subset_1 @ 
% 0.52/0.76              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.52/0.76              (u1_struct_0 @ sk_A))))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['46', '95'])).
% 0.52/0.76  thf('97', plain,
% 0.52/0.76      ((~ (r2_hidden @ 
% 0.52/0.76           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.52/0.76        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('clc', [status(thm)], ['15', '18'])).
% 0.52/0.76  thf('98', plain,
% 0.52/0.76      (((~ (m1_subset_1 @ 
% 0.52/0.76            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.52/0.76            (u1_struct_0 @ sk_A))
% 0.52/0.76         | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('clc', [status(thm)], ['96', '97'])).
% 0.52/0.76  thf('99', plain,
% 0.52/0.76      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.52/0.76        | (m1_subset_1 @ 
% 0.52/0.76           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.52/0.76           (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['20', '23'])).
% 0.52/0.76  thf('100', plain,
% 0.52/0.76      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.52/0.76         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('clc', [status(thm)], ['98', '99'])).
% 0.52/0.76  thf('101', plain,
% 0.52/0.76      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.52/0.76        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('102', plain,
% 0.52/0.76      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.52/0.76         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('split', [status(esa)], ['101'])).
% 0.52/0.76  thf('103', plain,
% 0.52/0.76      (((v1_subset_1 @ sk_B @ sk_B))
% 0.52/0.76         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.52/0.76             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('sup+', [status(thm)], ['100', '102'])).
% 0.52/0.76  thf(d7_subset_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.76       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.52/0.76  thf('104', plain,
% 0.52/0.76      (![X31 : $i, X32 : $i]:
% 0.52/0.76         (~ (v1_subset_1 @ X32 @ X31)
% 0.52/0.76          | ((X32) != (X31))
% 0.52/0.76          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 0.52/0.76      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.52/0.76  thf('105', plain,
% 0.52/0.76      (![X31 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X31))
% 0.52/0.76          | ~ (v1_subset_1 @ X31 @ X31))),
% 0.52/0.76      inference('simplify', [status(thm)], ['104'])).
% 0.52/0.76  thf('106', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.76  thf('107', plain, (![X31 : $i]: ~ (v1_subset_1 @ X31 @ X31)),
% 0.52/0.76      inference('demod', [status(thm)], ['105', '106'])).
% 0.52/0.76  thf('108', plain,
% 0.52/0.76      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.52/0.76       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['103', '107'])).
% 0.52/0.76  thf('109', plain,
% 0.52/0.76      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.52/0.76       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('split', [status(esa)], ['101'])).
% 0.52/0.76  thf('110', plain,
% 0.52/0.76      (![X17 : $i]:
% 0.52/0.76         (((k3_yellow_0 @ X17) = (k1_yellow_0 @ X17 @ k1_xboole_0))
% 0.52/0.76          | ~ (l1_orders_2 @ X17))),
% 0.52/0.76      inference('cnf', [status(esa)], [d11_yellow_0])).
% 0.52/0.76  thf('111', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('112', plain,
% 0.52/0.76      (![X31 : $i, X32 : $i]:
% 0.52/0.76         (((X32) = (X31))
% 0.52/0.76          | (v1_subset_1 @ X32 @ X31)
% 0.52/0.76          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 0.52/0.76      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.52/0.76  thf('113', plain,
% 0.52/0.76      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.52/0.76        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['111', '112'])).
% 0.52/0.76  thf('114', plain,
% 0.52/0.76      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.52/0.76         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('split', [status(esa)], ['0'])).
% 0.52/0.76  thf('115', plain,
% 0.52/0.76      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.52/0.76         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['113', '114'])).
% 0.52/0.76  thf('116', plain,
% 0.52/0.76      (![X22 : $i, X23 : $i]:
% 0.52/0.76         (~ (l1_orders_2 @ X22)
% 0.52/0.76          | (m1_subset_1 @ (k1_yellow_0 @ X22 @ X23) @ (u1_struct_0 @ X22)))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 0.52/0.76  thf('117', plain,
% 0.52/0.76      ((![X0 : $i]:
% 0.52/0.76          ((m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ sk_B)
% 0.52/0.76           | ~ (l1_orders_2 @ sk_A)))
% 0.52/0.76         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('sup+', [status(thm)], ['115', '116'])).
% 0.52/0.76  thf('118', plain, ((l1_orders_2 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('119', plain,
% 0.52/0.76      ((![X0 : $i]: (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ sk_B))
% 0.52/0.76         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('demod', [status(thm)], ['117', '118'])).
% 0.52/0.76  thf('120', plain,
% 0.52/0.76      ((((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B) | ~ (l1_orders_2 @ sk_A)))
% 0.52/0.76         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('sup+', [status(thm)], ['110', '119'])).
% 0.52/0.76  thf('121', plain, ((l1_orders_2 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('122', plain,
% 0.52/0.76      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.52/0.76         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('demod', [status(thm)], ['120', '121'])).
% 0.52/0.76  thf(t2_subset, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ A @ B ) =>
% 0.52/0.76       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.52/0.76  thf('123', plain,
% 0.52/0.76      (![X9 : $i, X10 : $i]:
% 0.52/0.76         ((r2_hidden @ X9 @ X10)
% 0.52/0.76          | (v1_xboole_0 @ X10)
% 0.52/0.76          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.52/0.76      inference('cnf', [status(esa)], [t2_subset])).
% 0.52/0.76  thf('124', plain,
% 0.52/0.76      ((((v1_xboole_0 @ sk_B) | (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.52/0.76         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['122', '123'])).
% 0.52/0.76  thf('125', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('126', plain,
% 0.52/0.76      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.52/0.76         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('clc', [status(thm)], ['124', '125'])).
% 0.52/0.76  thf('127', plain,
% 0.52/0.76      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.52/0.76         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.52/0.76      inference('split', [status(esa)], ['101'])).
% 0.52/0.76  thf('128', plain,
% 0.52/0.76      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.52/0.76       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['126', '127'])).
% 0.52/0.76  thf('129', plain, ($false),
% 0.52/0.76      inference('sat_resolution*', [status(thm)], ['1', '108', '109', '128'])).
% 0.52/0.76  
% 0.52/0.76  % SZS output end Refutation
% 0.52/0.76  
% 0.60/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
