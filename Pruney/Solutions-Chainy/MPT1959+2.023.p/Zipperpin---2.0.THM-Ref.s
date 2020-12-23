%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fho1adw7V1

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:12 EST 2020

% Result     : Theorem 27.24s
% Output     : Refutation 27.24s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 449 expanded)
%              Number of leaves         :   46 ( 147 expanded)
%              Depth                    :   26
%              Number of atoms          : 1796 (6607 expanded)
%              Number of equality atoms :   38 (  70 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ! [X33: $i] :
      ( ( r1_yellow_0 @ X33 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X33 )
      | ~ ( v1_yellow_0 @ X33 )
      | ~ ( v5_orders_2 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( sk_B @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('13',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( sk_B @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('14',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39 = X38 )
      | ( v1_subset_1 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X11: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

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

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( X10 = X8 )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X10 @ X9 ) @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

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

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( r2_hidden @ ( sk_D_1 @ X21 @ X23 @ X22 ) @ X23 )
      | ( r2_lattice3 @ X22 @ X23 @ X21 )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ k1_xboole_0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','27'])).

thf('29',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_orders_2 @ X30 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X30 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X28
       != ( k1_yellow_0 @ X26 @ X27 ) )
      | ~ ( r2_lattice3 @ X26 @ X27 @ X29 )
      | ( r1_orders_2 @ X26 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r1_yellow_0 @ X26 @ X27 )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d9_yellow_0])).

thf('32',plain,(
    ! [X26: $i,X27: $i,X29: $i] :
      ( ~ ( l1_orders_2 @ X26 )
      | ~ ( r1_yellow_0 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X26 ) )
      | ( r1_orders_2 @ X26 @ ( k1_yellow_0 @ X26 @ X27 ) @ X29 )
      | ~ ( r2_lattice3 @ X26 @ X27 @ X29 ) ) ),
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
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_yellow_0 @ sk_A @ k1_xboole_0 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ k1_xboole_0 ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_orders_2 @ X30 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X30 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf(d11_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k3_yellow_0 @ A )
        = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ) )).

thf('48',plain,(
    ! [X25: $i] :
      ( ( ( k3_yellow_0 @ X25 )
        = ( k1_yellow_0 @ X25 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d11_yellow_0])).

thf('49',plain,(
    ! [X33: $i] :
      ( ( r1_yellow_0 @ X33 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X33 )
      | ~ ( v1_yellow_0 @ X33 )
      | ~ ( v5_orders_2 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('51',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_orders_2 @ X30 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X30 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('52',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( r2_hidden @ ( sk_D_1 @ X21 @ X23 @ X22 ) @ X23 )
      | ( r2_lattice3 @ X22 @ X23 @ X21 )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 @ X0 ) @ X2 )
      | ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( r2_lattice3 @ X1 @ X0 @ ( k1_yellow_0 @ X1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D_1 @ ( k1_yellow_0 @ X1 @ X2 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_lattice3 @ X0 @ k1_xboole_0 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_orders_2 @ X30 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X30 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r2_lattice3 @ X0 @ X1 @ X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_yellow_0 @ X0 @ X2 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ X2 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_yellow_0 @ X1 @ k1_xboole_0 )
      | ( r1_orders_2 @ X1 @ ( k1_yellow_0 @ X1 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k1_yellow_0 @ X0 @ k1_xboole_0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v1_yellow_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_yellow_0 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ ( k1_yellow_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('69',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('73',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('74',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v13_waybel_0 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ( r2_hidden @ X36 @ X34 )
      | ~ ( r1_orders_2 @ X35 @ X37 @ X36 )
      | ~ ( r2_hidden @ X37 @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_orders_2 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v13_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v5_orders_2 @ sk_A )
        | ~ ( v1_yellow_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','83'])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
        | ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','90'])).

thf('92',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('95',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m1_subset_1 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('99',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 )
        | ~ ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X0 ) @ sk_B_1 )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('101',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X1 @ sk_B_1 )
        | ~ ( r1_orders_2 @ sk_A @ ( k1_yellow_0 @ sk_A @ X0 ) @ X1 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( sk_B_1
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('105',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( X10 = X8 )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X10 )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('109',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_1
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['102','109'])).

thf('111',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('112',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['113'])).

thf('115',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['112','114'])).

thf('116',plain,(
    ! [X11: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('118',plain,(
    ! [X11: $i] :
      ~ ( v1_subset_1 @ X11 @ X11 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['113'])).

thf('121',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39 = X38 )
      | ( v1_subset_1 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('123',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('125',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('126',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X32 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_orders_2 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('127',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['125','128'])).

thf('130',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('131',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['113'])).

thf('136',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B_1 )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','119','120','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fho1adw7V1
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:36:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 27.24/27.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 27.24/27.43  % Solved by: fo/fo7.sh
% 27.24/27.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 27.24/27.43  % done 9698 iterations in 26.966s
% 27.24/27.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 27.24/27.43  % SZS output start Refutation
% 27.24/27.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 27.24/27.43  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 27.24/27.43  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 27.24/27.43  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 27.24/27.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 27.24/27.43  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 27.24/27.43  thf(sk_B_1_type, type, sk_B_1: $i).
% 27.24/27.43  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 27.24/27.43  thf(r2_yellow_0_type, type, r2_yellow_0: $i > $i > $o).
% 27.24/27.43  thf(sk_A_type, type, sk_A: $i).
% 27.24/27.43  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 27.24/27.43  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 27.24/27.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 27.24/27.43  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 27.24/27.43  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 27.24/27.43  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 27.24/27.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 27.24/27.43  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 27.24/27.43  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 27.24/27.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 27.24/27.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 27.24/27.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 27.24/27.43  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 27.24/27.43  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 27.24/27.43  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 27.24/27.43  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 27.24/27.43  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 27.24/27.43  thf(sk_B_type, type, sk_B: $i > $i).
% 27.24/27.43  thf(t8_waybel_7, conjecture,
% 27.24/27.43    (![A:$i]:
% 27.24/27.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 27.24/27.43         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 27.24/27.43         ( l1_orders_2 @ A ) ) =>
% 27.24/27.43       ( ![B:$i]:
% 27.24/27.43         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 27.24/27.43             ( v13_waybel_0 @ B @ A ) & 
% 27.24/27.43             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 27.24/27.43           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 27.24/27.43             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 27.24/27.43  thf(zf_stmt_0, negated_conjecture,
% 27.24/27.43    (~( ![A:$i]:
% 27.24/27.43        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 27.24/27.43            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 27.24/27.43            ( l1_orders_2 @ A ) ) =>
% 27.24/27.43          ( ![B:$i]:
% 27.24/27.43            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 27.24/27.43                ( v13_waybel_0 @ B @ A ) & 
% 27.24/27.43                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 27.24/27.43              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 27.24/27.43                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 27.24/27.43    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 27.24/27.43  thf('0', plain,
% 27.24/27.43      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 27.24/27.43        | ~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('1', plain,
% 27.24/27.43      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 27.24/27.43       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('split', [status(esa)], ['0'])).
% 27.24/27.43  thf(t42_yellow_0, axiom,
% 27.24/27.43    (![A:$i]:
% 27.24/27.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 27.24/27.43         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 27.24/27.43       ( ( r1_yellow_0 @ A @ k1_xboole_0 ) & 
% 27.24/27.43         ( r2_yellow_0 @ A @ ( u1_struct_0 @ A ) ) ) ))).
% 27.24/27.43  thf('2', plain,
% 27.24/27.43      (![X33 : $i]:
% 27.24/27.43         ((r1_yellow_0 @ X33 @ k1_xboole_0)
% 27.24/27.43          | ~ (l1_orders_2 @ X33)
% 27.24/27.43          | ~ (v1_yellow_0 @ X33)
% 27.24/27.43          | ~ (v5_orders_2 @ X33)
% 27.24/27.43          | (v2_struct_0 @ X33))),
% 27.24/27.43      inference('cnf', [status(esa)], [t42_yellow_0])).
% 27.24/27.43  thf(d3_tarski, axiom,
% 27.24/27.43    (![A:$i,B:$i]:
% 27.24/27.43     ( ( r1_tarski @ A @ B ) <=>
% 27.24/27.43       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 27.24/27.43  thf('3', plain,
% 27.24/27.43      (![X1 : $i, X3 : $i]:
% 27.24/27.43         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 27.24/27.43      inference('cnf', [status(esa)], [d3_tarski])).
% 27.24/27.43  thf(t4_subset_1, axiom,
% 27.24/27.43    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 27.24/27.43  thf('4', plain,
% 27.24/27.43      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 27.24/27.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 27.24/27.43  thf(l3_subset_1, axiom,
% 27.24/27.43    (![A:$i,B:$i]:
% 27.24/27.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 27.24/27.43       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 27.24/27.43  thf('5', plain,
% 27.24/27.43      (![X4 : $i, X5 : $i, X6 : $i]:
% 27.24/27.43         (~ (r2_hidden @ X4 @ X5)
% 27.24/27.43          | (r2_hidden @ X4 @ X6)
% 27.24/27.43          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 27.24/27.43      inference('cnf', [status(esa)], [l3_subset_1])).
% 27.24/27.43  thf('6', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i]:
% 27.24/27.43         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 27.24/27.43      inference('sup-', [status(thm)], ['4', '5'])).
% 27.24/27.43  thf('7', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i]:
% 27.24/27.43         ((r1_tarski @ k1_xboole_0 @ X0)
% 27.24/27.43          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X1))),
% 27.24/27.43      inference('sup-', [status(thm)], ['3', '6'])).
% 27.24/27.43  thf('8', plain,
% 27.24/27.43      (![X1 : $i, X3 : $i]:
% 27.24/27.43         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 27.24/27.43      inference('cnf', [status(esa)], [d3_tarski])).
% 27.24/27.43  thf('9', plain,
% 27.24/27.43      (![X0 : $i]:
% 27.24/27.43         ((r1_tarski @ k1_xboole_0 @ X0) | (r1_tarski @ k1_xboole_0 @ X0))),
% 27.24/27.43      inference('sup-', [status(thm)], ['7', '8'])).
% 27.24/27.43  thf('10', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 27.24/27.43      inference('simplify', [status(thm)], ['9'])).
% 27.24/27.43  thf('11', plain,
% 27.24/27.43      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf(rc3_subset_1, axiom,
% 27.24/27.43    (![A:$i]:
% 27.24/27.43     ( ?[B:$i]:
% 27.24/27.43       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 27.24/27.43         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 27.24/27.43  thf('12', plain,
% 27.24/27.43      (![X11 : $i]: (m1_subset_1 @ (sk_B @ X11) @ (k1_zfmisc_1 @ X11))),
% 27.24/27.43      inference('cnf', [status(esa)], [rc3_subset_1])).
% 27.24/27.43  thf('13', plain,
% 27.24/27.43      (![X11 : $i]: (m1_subset_1 @ (sk_B @ X11) @ (k1_zfmisc_1 @ X11))),
% 27.24/27.43      inference('cnf', [status(esa)], [rc3_subset_1])).
% 27.24/27.43  thf(d7_subset_1, axiom,
% 27.24/27.43    (![A:$i,B:$i]:
% 27.24/27.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 27.24/27.43       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 27.24/27.43  thf('14', plain,
% 27.24/27.43      (![X38 : $i, X39 : $i]:
% 27.24/27.43         (((X39) = (X38))
% 27.24/27.43          | (v1_subset_1 @ X39 @ X38)
% 27.24/27.43          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 27.24/27.43      inference('cnf', [status(esa)], [d7_subset_1])).
% 27.24/27.43  thf('15', plain,
% 27.24/27.43      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['13', '14'])).
% 27.24/27.43  thf('16', plain, (![X11 : $i]: ~ (v1_subset_1 @ (sk_B @ X11) @ X11)),
% 27.24/27.43      inference('cnf', [status(esa)], [rc3_subset_1])).
% 27.24/27.43  thf('17', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 27.24/27.43      inference('clc', [status(thm)], ['15', '16'])).
% 27.24/27.43  thf('18', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 27.24/27.43      inference('demod', [status(thm)], ['12', '17'])).
% 27.24/27.43  thf(t8_subset_1, axiom,
% 27.24/27.43    (![A:$i,B:$i]:
% 27.24/27.43     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 27.24/27.43       ( ![C:$i]:
% 27.24/27.43         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 27.24/27.43           ( ( ![D:$i]:
% 27.24/27.43               ( ( m1_subset_1 @ D @ A ) =>
% 27.24/27.43                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 27.24/27.43             ( ( B ) = ( C ) ) ) ) ) ))).
% 27.24/27.43  thf('19', plain,
% 27.24/27.43      (![X8 : $i, X9 : $i, X10 : $i]:
% 27.24/27.43         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 27.24/27.43          | ((X10) = (X8))
% 27.24/27.43          | (m1_subset_1 @ (sk_D @ X8 @ X10 @ X9) @ X9)
% 27.24/27.43          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 27.24/27.43      inference('cnf', [status(esa)], [t8_subset_1])).
% 27.24/27.43  thf('20', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i]:
% 27.24/27.43         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 27.24/27.43          | (m1_subset_1 @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 27.24/27.43          | ((X1) = (X0)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['18', '19'])).
% 27.24/27.43  thf('21', plain,
% 27.24/27.43      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 27.24/27.43        | (m1_subset_1 @ 
% 27.24/27.43           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 27.24/27.43           (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['11', '20'])).
% 27.24/27.43  thf(d9_lattice3, axiom,
% 27.24/27.43    (![A:$i]:
% 27.24/27.43     ( ( l1_orders_2 @ A ) =>
% 27.24/27.43       ( ![B:$i,C:$i]:
% 27.24/27.43         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 27.24/27.43           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 27.24/27.43             ( ![D:$i]:
% 27.24/27.43               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 27.24/27.43                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 27.24/27.43  thf('22', plain,
% 27.24/27.43      (![X21 : $i, X22 : $i, X23 : $i]:
% 27.24/27.43         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 27.24/27.43          | (r2_hidden @ (sk_D_1 @ X21 @ X23 @ X22) @ X23)
% 27.24/27.43          | (r2_lattice3 @ X22 @ X23 @ X21)
% 27.24/27.43          | ~ (l1_orders_2 @ X22))),
% 27.24/27.43      inference('cnf', [status(esa)], [d9_lattice3])).
% 27.24/27.43  thf('23', plain,
% 27.24/27.43      (![X0 : $i]:
% 27.24/27.43         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 27.24/27.43          | ~ (l1_orders_2 @ sk_A)
% 27.24/27.43          | (r2_lattice3 @ sk_A @ X0 @ 
% 27.24/27.43             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 27.24/27.43          | (r2_hidden @ 
% 27.24/27.43             (sk_D_1 @ 
% 27.24/27.43              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 27.24/27.43              X0 @ sk_A) @ 
% 27.24/27.43             X0))),
% 27.24/27.43      inference('sup-', [status(thm)], ['21', '22'])).
% 27.24/27.43  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('25', plain,
% 27.24/27.43      (![X0 : $i]:
% 27.24/27.43         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 27.24/27.43          | (r2_lattice3 @ sk_A @ X0 @ 
% 27.24/27.43             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 27.24/27.43          | (r2_hidden @ 
% 27.24/27.43             (sk_D_1 @ 
% 27.24/27.43              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 27.24/27.43              X0 @ sk_A) @ 
% 27.24/27.43             X0))),
% 27.24/27.43      inference('demod', [status(thm)], ['23', '24'])).
% 27.24/27.43  thf(t7_ordinal1, axiom,
% 27.24/27.43    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 27.24/27.43  thf('26', plain,
% 27.24/27.43      (![X19 : $i, X20 : $i]:
% 27.24/27.43         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 27.24/27.43      inference('cnf', [status(esa)], [t7_ordinal1])).
% 27.24/27.43  thf('27', plain,
% 27.24/27.43      (![X0 : $i]:
% 27.24/27.43         ((r2_lattice3 @ sk_A @ X0 @ 
% 27.24/27.43           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 27.24/27.43          | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 27.24/27.43          | ~ (r1_tarski @ X0 @ 
% 27.24/27.43               (sk_D_1 @ 
% 27.24/27.43                (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 27.24/27.43                X0 @ sk_A)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['25', '26'])).
% 27.24/27.43  thf('28', plain,
% 27.24/27.43      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 27.24/27.43        | (r2_lattice3 @ sk_A @ k1_xboole_0 @ 
% 27.24/27.43           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 27.24/27.43      inference('sup-', [status(thm)], ['10', '27'])).
% 27.24/27.43  thf('29', plain,
% 27.24/27.43      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 27.24/27.43        | (m1_subset_1 @ 
% 27.24/27.43           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 27.24/27.43           (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['11', '20'])).
% 27.24/27.43  thf(dt_k1_yellow_0, axiom,
% 27.24/27.43    (![A:$i,B:$i]:
% 27.24/27.43     ( ( l1_orders_2 @ A ) =>
% 27.24/27.43       ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 27.24/27.43  thf('30', plain,
% 27.24/27.43      (![X30 : $i, X31 : $i]:
% 27.24/27.43         (~ (l1_orders_2 @ X30)
% 27.24/27.43          | (m1_subset_1 @ (k1_yellow_0 @ X30 @ X31) @ (u1_struct_0 @ X30)))),
% 27.24/27.43      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 27.24/27.43  thf(d9_yellow_0, axiom,
% 27.24/27.43    (![A:$i]:
% 27.24/27.43     ( ( l1_orders_2 @ A ) =>
% 27.24/27.43       ( ![B:$i,C:$i]:
% 27.24/27.43         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 27.24/27.43           ( ( r1_yellow_0 @ A @ B ) =>
% 27.24/27.43             ( ( ( C ) = ( k1_yellow_0 @ A @ B ) ) <=>
% 27.24/27.43               ( ( r2_lattice3 @ A @ B @ C ) & 
% 27.24/27.43                 ( ![D:$i]:
% 27.24/27.43                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 27.24/27.43                     ( ( r2_lattice3 @ A @ B @ D ) =>
% 27.24/27.43                       ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 27.24/27.43  thf('31', plain,
% 27.24/27.43      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 27.24/27.43         (((X28) != (k1_yellow_0 @ X26 @ X27))
% 27.24/27.43          | ~ (r2_lattice3 @ X26 @ X27 @ X29)
% 27.24/27.43          | (r1_orders_2 @ X26 @ X28 @ X29)
% 27.24/27.43          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X26))
% 27.24/27.43          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 27.24/27.43          | ~ (r1_yellow_0 @ X26 @ X27)
% 27.24/27.43          | ~ (l1_orders_2 @ X26))),
% 27.24/27.43      inference('cnf', [status(esa)], [d9_yellow_0])).
% 27.24/27.43  thf('32', plain,
% 27.24/27.43      (![X26 : $i, X27 : $i, X29 : $i]:
% 27.24/27.43         (~ (l1_orders_2 @ X26)
% 27.24/27.43          | ~ (r1_yellow_0 @ X26 @ X27)
% 27.24/27.43          | ~ (m1_subset_1 @ (k1_yellow_0 @ X26 @ X27) @ (u1_struct_0 @ X26))
% 27.24/27.43          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X26))
% 27.24/27.43          | (r1_orders_2 @ X26 @ (k1_yellow_0 @ X26 @ X27) @ X29)
% 27.24/27.43          | ~ (r2_lattice3 @ X26 @ X27 @ X29))),
% 27.24/27.43      inference('simplify', [status(thm)], ['31'])).
% 27.24/27.43  thf('33', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.24/27.43         (~ (l1_orders_2 @ X0)
% 27.24/27.43          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 27.24/27.43          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 27.24/27.43          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 27.24/27.43          | ~ (r1_yellow_0 @ X0 @ X1)
% 27.24/27.43          | ~ (l1_orders_2 @ X0))),
% 27.24/27.43      inference('sup-', [status(thm)], ['30', '32'])).
% 27.24/27.43  thf('34', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.24/27.43         (~ (r1_yellow_0 @ X0 @ X1)
% 27.24/27.43          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 27.24/27.43          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 27.24/27.43          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 27.24/27.43          | ~ (l1_orders_2 @ X0))),
% 27.24/27.43      inference('simplify', [status(thm)], ['33'])).
% 27.24/27.43  thf('35', plain,
% 27.24/27.43      (![X0 : $i]:
% 27.24/27.43         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 27.24/27.43          | ~ (l1_orders_2 @ sk_A)
% 27.24/27.43          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 27.24/27.43               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 27.24/27.43          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 27.24/27.43             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 27.24/27.43          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 27.24/27.43      inference('sup-', [status(thm)], ['29', '34'])).
% 27.24/27.43  thf('36', plain, ((l1_orders_2 @ sk_A)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('37', plain,
% 27.24/27.43      (![X0 : $i]:
% 27.24/27.43         (((sk_B_1) = (u1_struct_0 @ sk_A))
% 27.24/27.43          | ~ (r2_lattice3 @ sk_A @ X0 @ 
% 27.24/27.43               (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 27.24/27.43          | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ 
% 27.24/27.43             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 27.24/27.43          | ~ (r1_yellow_0 @ sk_A @ X0))),
% 27.24/27.43      inference('demod', [status(thm)], ['35', '36'])).
% 27.24/27.43  thf('38', plain,
% 27.24/27.43      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 27.24/27.43        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 27.24/27.43        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 27.24/27.43           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 27.24/27.43        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['28', '37'])).
% 27.24/27.43  thf('39', plain,
% 27.24/27.43      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 27.24/27.43         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 27.24/27.43        | ~ (r1_yellow_0 @ sk_A @ k1_xboole_0)
% 27.24/27.43        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('simplify', [status(thm)], ['38'])).
% 27.24/27.43  thf('40', plain,
% 27.24/27.43      (((v2_struct_0 @ sk_A)
% 27.24/27.43        | ~ (v5_orders_2 @ sk_A)
% 27.24/27.43        | ~ (v1_yellow_0 @ sk_A)
% 27.24/27.43        | ~ (l1_orders_2 @ sk_A)
% 27.24/27.43        | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 27.24/27.43        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 27.24/27.43           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 27.24/27.43      inference('sup-', [status(thm)], ['2', '39'])).
% 27.24/27.43  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('42', plain, ((v1_yellow_0 @ sk_A)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('44', plain,
% 27.24/27.43      (((v2_struct_0 @ sk_A)
% 27.24/27.43        | ((sk_B_1) = (u1_struct_0 @ sk_A))
% 27.24/27.43        | (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 27.24/27.43           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 27.24/27.43      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 27.24/27.43  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('46', plain,
% 27.24/27.43      (((r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ k1_xboole_0) @ 
% 27.24/27.43         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 27.24/27.43        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('clc', [status(thm)], ['44', '45'])).
% 27.24/27.43  thf('47', plain,
% 27.24/27.43      (![X30 : $i, X31 : $i]:
% 27.24/27.43         (~ (l1_orders_2 @ X30)
% 27.24/27.43          | (m1_subset_1 @ (k1_yellow_0 @ X30 @ X31) @ (u1_struct_0 @ X30)))),
% 27.24/27.43      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 27.24/27.43  thf(d11_yellow_0, axiom,
% 27.24/27.43    (![A:$i]:
% 27.24/27.43     ( ( l1_orders_2 @ A ) =>
% 27.24/27.43       ( ( k3_yellow_0 @ A ) = ( k1_yellow_0 @ A @ k1_xboole_0 ) ) ))).
% 27.24/27.43  thf('48', plain,
% 27.24/27.43      (![X25 : $i]:
% 27.24/27.43         (((k3_yellow_0 @ X25) = (k1_yellow_0 @ X25 @ k1_xboole_0))
% 27.24/27.43          | ~ (l1_orders_2 @ X25))),
% 27.24/27.43      inference('cnf', [status(esa)], [d11_yellow_0])).
% 27.24/27.43  thf('49', plain,
% 27.24/27.43      (![X33 : $i]:
% 27.24/27.43         ((r1_yellow_0 @ X33 @ k1_xboole_0)
% 27.24/27.43          | ~ (l1_orders_2 @ X33)
% 27.24/27.43          | ~ (v1_yellow_0 @ X33)
% 27.24/27.43          | ~ (v5_orders_2 @ X33)
% 27.24/27.43          | (v2_struct_0 @ X33))),
% 27.24/27.43      inference('cnf', [status(esa)], [t42_yellow_0])).
% 27.24/27.43  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 27.24/27.43      inference('simplify', [status(thm)], ['9'])).
% 27.24/27.43  thf('51', plain,
% 27.24/27.43      (![X30 : $i, X31 : $i]:
% 27.24/27.43         (~ (l1_orders_2 @ X30)
% 27.24/27.43          | (m1_subset_1 @ (k1_yellow_0 @ X30 @ X31) @ (u1_struct_0 @ X30)))),
% 27.24/27.43      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 27.24/27.43  thf('52', plain,
% 27.24/27.43      (![X21 : $i, X22 : $i, X23 : $i]:
% 27.24/27.43         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 27.24/27.43          | (r2_hidden @ (sk_D_1 @ X21 @ X23 @ X22) @ X23)
% 27.24/27.43          | (r2_lattice3 @ X22 @ X23 @ X21)
% 27.24/27.43          | ~ (l1_orders_2 @ X22))),
% 27.24/27.43      inference('cnf', [status(esa)], [d9_lattice3])).
% 27.24/27.43  thf('53', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.24/27.43         (~ (l1_orders_2 @ X0)
% 27.24/27.43          | ~ (l1_orders_2 @ X0)
% 27.24/27.43          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 27.24/27.43          | (r2_hidden @ (sk_D_1 @ (k1_yellow_0 @ X0 @ X1) @ X2 @ X0) @ X2))),
% 27.24/27.43      inference('sup-', [status(thm)], ['51', '52'])).
% 27.24/27.43  thf('54', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.24/27.43         ((r2_hidden @ (sk_D_1 @ (k1_yellow_0 @ X0 @ X1) @ X2 @ X0) @ X2)
% 27.24/27.43          | (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 27.24/27.43          | ~ (l1_orders_2 @ X0))),
% 27.24/27.43      inference('simplify', [status(thm)], ['53'])).
% 27.24/27.43  thf('55', plain,
% 27.24/27.43      (![X19 : $i, X20 : $i]:
% 27.24/27.43         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 27.24/27.43      inference('cnf', [status(esa)], [t7_ordinal1])).
% 27.24/27.43  thf('56', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.24/27.43         (~ (l1_orders_2 @ X1)
% 27.24/27.43          | (r2_lattice3 @ X1 @ X0 @ (k1_yellow_0 @ X1 @ X2))
% 27.24/27.43          | ~ (r1_tarski @ X0 @ (sk_D_1 @ (k1_yellow_0 @ X1 @ X2) @ X0 @ X1)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['54', '55'])).
% 27.24/27.43  thf('57', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i]:
% 27.24/27.43         ((r2_lattice3 @ X0 @ k1_xboole_0 @ (k1_yellow_0 @ X0 @ X1))
% 27.24/27.43          | ~ (l1_orders_2 @ X0))),
% 27.24/27.43      inference('sup-', [status(thm)], ['50', '56'])).
% 27.24/27.43  thf('58', plain,
% 27.24/27.43      (![X30 : $i, X31 : $i]:
% 27.24/27.43         (~ (l1_orders_2 @ X30)
% 27.24/27.43          | (m1_subset_1 @ (k1_yellow_0 @ X30 @ X31) @ (u1_struct_0 @ X30)))),
% 27.24/27.43      inference('cnf', [status(esa)], [dt_k1_yellow_0])).
% 27.24/27.43  thf('59', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.24/27.43         (~ (r1_yellow_0 @ X0 @ X1)
% 27.24/27.43          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 27.24/27.43          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X1) @ X2)
% 27.24/27.43          | ~ (r2_lattice3 @ X0 @ X1 @ X2)
% 27.24/27.43          | ~ (l1_orders_2 @ X0))),
% 27.24/27.43      inference('simplify', [status(thm)], ['33'])).
% 27.24/27.43  thf('60', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.24/27.43         (~ (l1_orders_2 @ X0)
% 27.24/27.43          | ~ (l1_orders_2 @ X0)
% 27.24/27.43          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 27.24/27.43          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 27.24/27.43             (k1_yellow_0 @ X0 @ X1))
% 27.24/27.43          | ~ (r1_yellow_0 @ X0 @ X2))),
% 27.24/27.43      inference('sup-', [status(thm)], ['58', '59'])).
% 27.24/27.43  thf('61', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.24/27.43         (~ (r1_yellow_0 @ X0 @ X2)
% 27.24/27.43          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ X2) @ 
% 27.24/27.43             (k1_yellow_0 @ X0 @ X1))
% 27.24/27.43          | ~ (r2_lattice3 @ X0 @ X2 @ (k1_yellow_0 @ X0 @ X1))
% 27.24/27.43          | ~ (l1_orders_2 @ X0))),
% 27.24/27.43      inference('simplify', [status(thm)], ['60'])).
% 27.24/27.43  thf('62', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i]:
% 27.24/27.43         (~ (l1_orders_2 @ X1)
% 27.24/27.43          | ~ (l1_orders_2 @ X1)
% 27.24/27.43          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 27.24/27.43             (k1_yellow_0 @ X1 @ X0))
% 27.24/27.43          | ~ (r1_yellow_0 @ X1 @ k1_xboole_0))),
% 27.24/27.43      inference('sup-', [status(thm)], ['57', '61'])).
% 27.24/27.43  thf('63', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i]:
% 27.24/27.43         (~ (r1_yellow_0 @ X1 @ k1_xboole_0)
% 27.24/27.43          | (r1_orders_2 @ X1 @ (k1_yellow_0 @ X1 @ k1_xboole_0) @ 
% 27.24/27.43             (k1_yellow_0 @ X1 @ X0))
% 27.24/27.43          | ~ (l1_orders_2 @ X1))),
% 27.24/27.43      inference('simplify', [status(thm)], ['62'])).
% 27.24/27.43  thf('64', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i]:
% 27.24/27.43         ((v2_struct_0 @ X0)
% 27.24/27.43          | ~ (v5_orders_2 @ X0)
% 27.24/27.43          | ~ (v1_yellow_0 @ X0)
% 27.24/27.43          | ~ (l1_orders_2 @ X0)
% 27.24/27.43          | ~ (l1_orders_2 @ X0)
% 27.24/27.43          | (r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 27.24/27.43             (k1_yellow_0 @ X0 @ X1)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['49', '63'])).
% 27.24/27.43  thf('65', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i]:
% 27.24/27.43         ((r1_orders_2 @ X0 @ (k1_yellow_0 @ X0 @ k1_xboole_0) @ 
% 27.24/27.43           (k1_yellow_0 @ X0 @ X1))
% 27.24/27.43          | ~ (l1_orders_2 @ X0)
% 27.24/27.43          | ~ (v1_yellow_0 @ X0)
% 27.24/27.43          | ~ (v5_orders_2 @ X0)
% 27.24/27.43          | (v2_struct_0 @ X0))),
% 27.24/27.43      inference('simplify', [status(thm)], ['64'])).
% 27.24/27.43  thf('66', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i]:
% 27.24/27.43         ((r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1))
% 27.24/27.43          | ~ (l1_orders_2 @ X0)
% 27.24/27.43          | (v2_struct_0 @ X0)
% 27.24/27.43          | ~ (v5_orders_2 @ X0)
% 27.24/27.43          | ~ (v1_yellow_0 @ X0)
% 27.24/27.43          | ~ (l1_orders_2 @ X0))),
% 27.24/27.43      inference('sup+', [status(thm)], ['48', '65'])).
% 27.24/27.43  thf('67', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i]:
% 27.24/27.43         (~ (v1_yellow_0 @ X0)
% 27.24/27.43          | ~ (v5_orders_2 @ X0)
% 27.24/27.43          | (v2_struct_0 @ X0)
% 27.24/27.43          | ~ (l1_orders_2 @ X0)
% 27.24/27.43          | (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ (k1_yellow_0 @ X0 @ X1)))),
% 27.24/27.43      inference('simplify', [status(thm)], ['66'])).
% 27.24/27.43  thf('68', plain,
% 27.24/27.43      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('split', [status(esa)], ['0'])).
% 27.24/27.43  thf('69', plain,
% 27.24/27.43      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('70', plain,
% 27.24/27.43      (![X4 : $i, X5 : $i, X6 : $i]:
% 27.24/27.43         (~ (r2_hidden @ X4 @ X5)
% 27.24/27.43          | (r2_hidden @ X4 @ X6)
% 27.24/27.43          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 27.24/27.43      inference('cnf', [status(esa)], [l3_subset_1])).
% 27.24/27.43  thf('71', plain,
% 27.24/27.43      (![X0 : $i]:
% 27.24/27.43         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 27.24/27.43      inference('sup-', [status(thm)], ['69', '70'])).
% 27.24/27.43  thf('72', plain,
% 27.24/27.43      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['68', '71'])).
% 27.24/27.43  thf(t1_subset, axiom,
% 27.24/27.43    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 27.24/27.43  thf('73', plain,
% 27.24/27.43      (![X12 : $i, X13 : $i]:
% 27.24/27.43         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 27.24/27.43      inference('cnf', [status(esa)], [t1_subset])).
% 27.24/27.43  thf('74', plain,
% 27.24/27.43      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['72', '73'])).
% 27.24/27.43  thf('75', plain,
% 27.24/27.43      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf(d20_waybel_0, axiom,
% 27.24/27.43    (![A:$i]:
% 27.24/27.43     ( ( l1_orders_2 @ A ) =>
% 27.24/27.43       ( ![B:$i]:
% 27.24/27.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.24/27.43           ( ( v13_waybel_0 @ B @ A ) <=>
% 27.24/27.43             ( ![C:$i]:
% 27.24/27.43               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 27.24/27.43                 ( ![D:$i]:
% 27.24/27.43                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 27.24/27.43                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 27.24/27.43                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 27.24/27.43  thf('76', plain,
% 27.24/27.43      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 27.24/27.43         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 27.24/27.43          | ~ (v13_waybel_0 @ X34 @ X35)
% 27.24/27.43          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 27.24/27.43          | (r2_hidden @ X36 @ X34)
% 27.24/27.43          | ~ (r1_orders_2 @ X35 @ X37 @ X36)
% 27.24/27.43          | ~ (r2_hidden @ X37 @ X34)
% 27.24/27.43          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 27.24/27.43          | ~ (l1_orders_2 @ X35))),
% 27.24/27.43      inference('cnf', [status(esa)], [d20_waybel_0])).
% 27.24/27.43  thf('77', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i]:
% 27.24/27.43         (~ (l1_orders_2 @ sk_A)
% 27.24/27.43          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 27.24/27.43          | ~ (r2_hidden @ X0 @ sk_B_1)
% 27.24/27.43          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 27.24/27.43          | (r2_hidden @ X1 @ sk_B_1)
% 27.24/27.43          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 27.24/27.43          | ~ (v13_waybel_0 @ sk_B_1 @ sk_A))),
% 27.24/27.43      inference('sup-', [status(thm)], ['75', '76'])).
% 27.24/27.43  thf('78', plain, ((l1_orders_2 @ sk_A)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('79', plain, ((v13_waybel_0 @ sk_B_1 @ sk_A)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('80', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i]:
% 27.24/27.43         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 27.24/27.43          | ~ (r2_hidden @ X0 @ sk_B_1)
% 27.24/27.43          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 27.24/27.43          | (r2_hidden @ X1 @ sk_B_1)
% 27.24/27.43          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('demod', [status(thm)], ['77', '78', '79'])).
% 27.24/27.43  thf('81', plain,
% 27.24/27.43      ((![X0 : $i]:
% 27.24/27.43          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 27.24/27.43           | (r2_hidden @ X0 @ sk_B_1)
% 27.24/27.43           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 27.24/27.43           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['74', '80'])).
% 27.24/27.43  thf('82', plain,
% 27.24/27.43      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('split', [status(esa)], ['0'])).
% 27.24/27.43  thf('83', plain,
% 27.24/27.43      ((![X0 : $i]:
% 27.24/27.43          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 27.24/27.43           | (r2_hidden @ X0 @ sk_B_1)
% 27.24/27.43           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('demod', [status(thm)], ['81', '82'])).
% 27.24/27.43  thf('84', plain,
% 27.24/27.43      ((![X0 : $i]:
% 27.24/27.43          (~ (l1_orders_2 @ sk_A)
% 27.24/27.43           | (v2_struct_0 @ sk_A)
% 27.24/27.43           | ~ (v5_orders_2 @ sk_A)
% 27.24/27.43           | ~ (v1_yellow_0 @ sk_A)
% 27.24/27.43           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 27.24/27.43           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['67', '83'])).
% 27.24/27.43  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('86', plain, ((v5_orders_2 @ sk_A)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('87', plain, ((v1_yellow_0 @ sk_A)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('88', plain,
% 27.24/27.43      ((![X0 : $i]:
% 27.24/27.43          ((v2_struct_0 @ sk_A)
% 27.24/27.43           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)
% 27.24/27.43           | ~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 27.24/27.43  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('90', plain,
% 27.24/27.43      ((![X0 : $i]:
% 27.24/27.43          (~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A))
% 27.24/27.43           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('clc', [status(thm)], ['88', '89'])).
% 27.24/27.43  thf('91', plain,
% 27.24/27.43      ((![X0 : $i]:
% 27.24/27.43          (~ (l1_orders_2 @ sk_A)
% 27.24/27.43           | (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['47', '90'])).
% 27.24/27.43  thf('92', plain, ((l1_orders_2 @ sk_A)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('93', plain,
% 27.24/27.43      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('demod', [status(thm)], ['91', '92'])).
% 27.24/27.43  thf('94', plain,
% 27.24/27.43      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf(t4_subset, axiom,
% 27.24/27.43    (![A:$i,B:$i,C:$i]:
% 27.24/27.43     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 27.24/27.43       ( m1_subset_1 @ A @ C ) ))).
% 27.24/27.43  thf('95', plain,
% 27.24/27.43      (![X16 : $i, X17 : $i, X18 : $i]:
% 27.24/27.43         (~ (r2_hidden @ X16 @ X17)
% 27.24/27.43          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 27.24/27.43          | (m1_subset_1 @ X16 @ X18))),
% 27.24/27.43      inference('cnf', [status(esa)], [t4_subset])).
% 27.24/27.43  thf('96', plain,
% 27.24/27.43      (![X0 : $i]:
% 27.24/27.43         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 27.24/27.43          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 27.24/27.43      inference('sup-', [status(thm)], ['94', '95'])).
% 27.24/27.43  thf('97', plain,
% 27.24/27.43      ((![X0 : $i]:
% 27.24/27.43          (m1_subset_1 @ (k1_yellow_0 @ sk_A @ X0) @ (u1_struct_0 @ sk_A)))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['93', '96'])).
% 27.24/27.43  thf('98', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i]:
% 27.24/27.43         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 27.24/27.43          | ~ (r2_hidden @ X0 @ sk_B_1)
% 27.24/27.43          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 27.24/27.43          | (r2_hidden @ X1 @ sk_B_1)
% 27.24/27.43          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('demod', [status(thm)], ['77', '78', '79'])).
% 27.24/27.43  thf('99', plain,
% 27.24/27.43      ((![X0 : $i, X1 : $i]:
% 27.24/27.43          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 27.24/27.43           | (r2_hidden @ X1 @ sk_B_1)
% 27.24/27.43           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)
% 27.24/27.43           | ~ (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1)))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['97', '98'])).
% 27.24/27.43  thf('100', plain,
% 27.24/27.43      ((![X0 : $i]: (r2_hidden @ (k1_yellow_0 @ sk_A @ X0) @ sk_B_1))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('demod', [status(thm)], ['91', '92'])).
% 27.24/27.43  thf('101', plain,
% 27.24/27.43      ((![X0 : $i, X1 : $i]:
% 27.24/27.43          (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 27.24/27.43           | (r2_hidden @ X1 @ sk_B_1)
% 27.24/27.43           | ~ (r1_orders_2 @ sk_A @ (k1_yellow_0 @ sk_A @ X0) @ X1)))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('demod', [status(thm)], ['99', '100'])).
% 27.24/27.43  thf('102', plain,
% 27.24/27.43      (((((sk_B_1) = (u1_struct_0 @ sk_A))
% 27.24/27.43         | (r2_hidden @ 
% 27.24/27.43            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 27.24/27.43            sk_B_1)
% 27.24/27.43         | ~ (m1_subset_1 @ 
% 27.24/27.43              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 27.24/27.43              (u1_struct_0 @ sk_A))))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['46', '101'])).
% 27.24/27.43  thf('103', plain,
% 27.24/27.43      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('104', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 27.24/27.43      inference('demod', [status(thm)], ['12', '17'])).
% 27.24/27.43  thf('105', plain,
% 27.24/27.43      (![X8 : $i, X9 : $i, X10 : $i]:
% 27.24/27.43         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 27.24/27.43          | ((X10) = (X8))
% 27.24/27.43          | ~ (r2_hidden @ (sk_D @ X8 @ X10 @ X9) @ X10)
% 27.24/27.43          | ~ (r2_hidden @ (sk_D @ X8 @ X10 @ X9) @ X8)
% 27.24/27.43          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 27.24/27.43      inference('cnf', [status(esa)], [t8_subset_1])).
% 27.24/27.43  thf('106', plain,
% 27.24/27.43      (![X0 : $i, X1 : $i]:
% 27.24/27.43         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 27.24/27.43          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 27.24/27.43          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 27.24/27.43          | ((X1) = (X0)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['104', '105'])).
% 27.24/27.43  thf('107', plain,
% 27.24/27.43      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 27.24/27.43        | ~ (r2_hidden @ 
% 27.24/27.43             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 27.24/27.43             sk_B_1)
% 27.24/27.43        | ~ (r2_hidden @ 
% 27.24/27.43             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 27.24/27.43             (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['103', '106'])).
% 27.24/27.43  thf('108', plain,
% 27.24/27.43      (![X0 : $i]:
% 27.24/27.43         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 27.24/27.43      inference('sup-', [status(thm)], ['69', '70'])).
% 27.24/27.43  thf('109', plain,
% 27.24/27.43      ((~ (r2_hidden @ 
% 27.24/27.43           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 27.24/27.43           sk_B_1)
% 27.24/27.43        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('clc', [status(thm)], ['107', '108'])).
% 27.24/27.43  thf('110', plain,
% 27.24/27.43      (((~ (m1_subset_1 @ 
% 27.24/27.43            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 27.24/27.43            (u1_struct_0 @ sk_A))
% 27.24/27.43         | ((sk_B_1) = (u1_struct_0 @ sk_A))))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('clc', [status(thm)], ['102', '109'])).
% 27.24/27.43  thf('111', plain,
% 27.24/27.43      ((((sk_B_1) = (u1_struct_0 @ sk_A))
% 27.24/27.43        | (m1_subset_1 @ 
% 27.24/27.43           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ 
% 27.24/27.43           (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['11', '20'])).
% 27.24/27.43  thf('112', plain,
% 27.24/27.43      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 27.24/27.43         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('clc', [status(thm)], ['110', '111'])).
% 27.24/27.43  thf('113', plain,
% 27.24/27.43      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 27.24/27.43        | (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('114', plain,
% 27.24/27.43      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 27.24/27.43         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 27.24/27.43      inference('split', [status(esa)], ['113'])).
% 27.24/27.43  thf('115', plain,
% 27.24/27.43      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 27.24/27.43         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) & 
% 27.24/27.43             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('sup+', [status(thm)], ['112', '114'])).
% 27.24/27.43  thf('116', plain, (![X11 : $i]: ~ (v1_subset_1 @ (sk_B @ X11) @ X11)),
% 27.24/27.43      inference('cnf', [status(esa)], [rc3_subset_1])).
% 27.24/27.43  thf('117', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 27.24/27.43      inference('clc', [status(thm)], ['15', '16'])).
% 27.24/27.43  thf('118', plain, (![X11 : $i]: ~ (v1_subset_1 @ X11 @ X11)),
% 27.24/27.43      inference('demod', [status(thm)], ['116', '117'])).
% 27.24/27.43  thf('119', plain,
% 27.24/27.43      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 27.24/27.43       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['115', '118'])).
% 27.24/27.43  thf('120', plain,
% 27.24/27.43      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 27.24/27.43       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('split', [status(esa)], ['113'])).
% 27.24/27.43  thf('121', plain,
% 27.24/27.43      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('122', plain,
% 27.24/27.43      (![X38 : $i, X39 : $i]:
% 27.24/27.43         (((X39) = (X38))
% 27.24/27.43          | (v1_subset_1 @ X39 @ X38)
% 27.24/27.43          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 27.24/27.43      inference('cnf', [status(esa)], [d7_subset_1])).
% 27.24/27.43  thf('123', plain,
% 27.24/27.43      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 27.24/27.43        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['121', '122'])).
% 27.24/27.43  thf('124', plain,
% 27.24/27.43      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 27.24/27.43         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 27.24/27.43      inference('split', [status(esa)], ['0'])).
% 27.24/27.43  thf('125', plain,
% 27.24/27.43      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 27.24/27.43         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 27.24/27.43      inference('sup-', [status(thm)], ['123', '124'])).
% 27.24/27.43  thf(dt_k3_yellow_0, axiom,
% 27.24/27.43    (![A:$i]:
% 27.24/27.43     ( ( l1_orders_2 @ A ) =>
% 27.24/27.43       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 27.24/27.43  thf('126', plain,
% 27.24/27.43      (![X32 : $i]:
% 27.24/27.43         ((m1_subset_1 @ (k3_yellow_0 @ X32) @ (u1_struct_0 @ X32))
% 27.24/27.43          | ~ (l1_orders_2 @ X32))),
% 27.24/27.43      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 27.24/27.43  thf(t2_subset, axiom,
% 27.24/27.43    (![A:$i,B:$i]:
% 27.24/27.43     ( ( m1_subset_1 @ A @ B ) =>
% 27.24/27.43       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 27.24/27.43  thf('127', plain,
% 27.24/27.43      (![X14 : $i, X15 : $i]:
% 27.24/27.43         ((r2_hidden @ X14 @ X15)
% 27.24/27.43          | (v1_xboole_0 @ X15)
% 27.24/27.43          | ~ (m1_subset_1 @ X14 @ X15))),
% 27.24/27.43      inference('cnf', [status(esa)], [t2_subset])).
% 27.24/27.43  thf('128', plain,
% 27.24/27.43      (![X0 : $i]:
% 27.24/27.43         (~ (l1_orders_2 @ X0)
% 27.24/27.43          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 27.24/27.43          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['126', '127'])).
% 27.24/27.43  thf('129', plain,
% 27.24/27.43      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)
% 27.24/27.43         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 27.24/27.43         | ~ (l1_orders_2 @ sk_A)))
% 27.24/27.43         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 27.24/27.43      inference('sup+', [status(thm)], ['125', '128'])).
% 27.24/27.43  thf('130', plain,
% 27.24/27.43      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 27.24/27.43         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 27.24/27.43      inference('sup-', [status(thm)], ['123', '124'])).
% 27.24/27.43  thf('131', plain, ((l1_orders_2 @ sk_A)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('132', plain,
% 27.24/27.43      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1) | (v1_xboole_0 @ sk_B_1)))
% 27.24/27.43         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 27.24/27.43      inference('demod', [status(thm)], ['129', '130', '131'])).
% 27.24/27.43  thf('133', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 27.24/27.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.24/27.43  thf('134', plain,
% 27.24/27.43      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 27.24/27.43         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 27.24/27.43      inference('clc', [status(thm)], ['132', '133'])).
% 27.24/27.43  thf('135', plain,
% 27.24/27.43      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1))
% 27.24/27.43         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)))),
% 27.24/27.43      inference('split', [status(esa)], ['113'])).
% 27.24/27.43  thf('136', plain,
% 27.24/27.43      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B_1)) | 
% 27.24/27.43       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 27.24/27.43      inference('sup-', [status(thm)], ['134', '135'])).
% 27.24/27.43  thf('137', plain, ($false),
% 27.24/27.43      inference('sat_resolution*', [status(thm)], ['1', '119', '120', '136'])).
% 27.24/27.43  
% 27.24/27.43  % SZS output end Refutation
% 27.24/27.43  
% 27.24/27.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
