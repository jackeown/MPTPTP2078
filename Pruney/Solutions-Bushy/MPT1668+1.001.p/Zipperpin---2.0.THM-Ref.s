%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1668+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rSaOJvdEHo

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:58 EST 2020

% Result     : Theorem 18.11s
% Output     : Refutation 18.11s
% Verified   : 
% Statistics : Number of formulae       :  239 ( 650 expanded)
%              Number of leaves         :   34 ( 192 expanded)
%              Depth                    :   23
%              Number of atoms          : 2643 (12981 expanded)
%              Number of equality atoms :   33 ( 312 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(v14_waybel_0_type,type,(
    v14_waybel_0: $i > $i > $o )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(t48_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_waybel_0 @ B @ A )
            & ( v12_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v14_waybel_0 @ B @ A )
          <=> ? [C: $i] :
                ( ( B
                  = ( k5_waybel_0 @ A @ C ) )
                & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_waybel_0 @ B @ A )
              & ( v12_waybel_0 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v14_waybel_0 @ B @ A )
            <=> ? [C: $i] :
                  ( ( B
                    = ( k5_waybel_0 @ A @ C ) )
                  & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_waybel_0])).

thf('0',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) )
    | ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) )
    | ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X35: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
       != ( k5_waybel_0 @ sk_A @ X35 ) )
      | ~ ( v14_waybel_0 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X35: $i] :
        ( ( sk_B
         != ( k5_waybel_0 @ sk_A @ X35 ) )
        | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( m1_subset_1 @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,
    ( ( sk_B
      = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
    | ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v14_waybel_0 @ sk_B @ sk_A )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d21_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_waybel_0 @ B @ A )
            & ( v12_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v14_waybel_0 @ B @ A )
          <=> ? [C: $i] :
                ( ( r2_lattice3 @ A @ B @ C )
                & ( r2_hidden @ C @ B )
                & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( v1_waybel_0 @ X7 @ X8 )
      | ~ ( v12_waybel_0 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v14_waybel_0 @ X7 @ X8 )
      | ( r2_lattice3 @ X8 @ X7 @ ( sk_C_1 @ X7 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d21_waybel_0])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v14_waybel_0 @ sk_B @ sk_A )
    | ~ ( v12_waybel_0 @ sk_B @ sk_A )
    | ~ ( v1_waybel_0 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v14_waybel_0 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16','17','18','19'])).

thf('21',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_C_1 @ sk_B @ sk_A ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v14_waybel_0 @ sk_B @ sk_A )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( v1_waybel_0 @ X7 @ X8 )
      | ~ ( v12_waybel_0 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v14_waybel_0 @ X7 @ X8 )
      | ( m1_subset_1 @ ( sk_C_1 @ X7 @ X8 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d21_waybel_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v14_waybel_0 @ sk_B @ sk_A )
    | ~ ( v12_waybel_0 @ sk_B @ sk_A )
    | ~ ( v1_waybel_0 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v14_waybel_0 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31','32','33','34'])).

thf('36',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

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

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r2_lattice3 @ X15 @ X16 @ X14 )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ( r1_orders_2 @ X15 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('42',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ X1 )
        | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ X1 )
        | ~ ( r2_lattice3 @ sk_A @ X1 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r1_orders_2 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r1_orders_2 @ sk_A @ ( sk_C_2 @ X0 @ sk_B ) @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(t17_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k5_waybel_0 @ A @ B ) )
              <=> ( r1_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf('50',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r1_orders_2 @ X27 @ X28 @ X26 )
      | ( r2_hidden @ X28 @ ( k5_waybel_0 @ X27 @ X26 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B ) @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ ( sk_C_2 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B ) @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B ) @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_B ) @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X13 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X13 @ X11 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,
    ( ( ( r1_tarski @ sk_B @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r1_tarski @ sk_B @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['60'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,
    ( ( ~ ( r1_tarski @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_B )
      | ( ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) )
        = sk_B ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(dt_k5_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k5_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('66',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( m1_subset_1 @ ( k5_waybel_0 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_waybel_0])).

thf('67',plain,
    ( ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( m1_subset_1 @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ X0 )
        | ( m1_subset_1 @ ( sk_C_2 @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('75',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('76',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('77',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r2_hidden @ X28 @ ( k5_waybel_0 @ X27 @ X26 ) )
      | ( r1_orders_2 @ X27 @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ X0 )
        | ( r1_orders_2 @ sk_A @ ( sk_C_2 @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ ( sk_C_2 @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_orders_2 @ sk_A @ ( sk_C_2 @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
        | ( r1_tarski @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ X0 ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( r1_orders_2 @ sk_A @ ( sk_C_2 @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) @ ( sk_C_1 @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ X0 ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ X0 )
        | ( r1_orders_2 @ sk_A @ ( sk_C_2 @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v12_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ B )
                        & ( r1_orders_2 @ A @ D @ C ) )
                     => ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('88',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v12_waybel_0 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r2_hidden @ X5 @ X3 )
      | ~ ( r1_orders_2 @ X4 @ X5 @ X6 )
      | ~ ( r2_hidden @ X6 @ X3 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d19_waybel_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v12_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,
    ( ( v14_waybel_0 @ sk_B @ sk_A )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( v1_waybel_0 @ X7 @ X8 )
      | ~ ( v12_waybel_0 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v14_waybel_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X7 )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d21_waybel_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v14_waybel_0 @ sk_B @ sk_A )
    | ~ ( v12_waybel_0 @ sk_B @ sk_A )
    | ~ ( v1_waybel_0 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v14_waybel_0 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98','99','100','101','102'])).

thf('104',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['94','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['93','108'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ X0 )
        | ( r2_hidden @ ( sk_C_2 @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) @ sk_B )
        | ~ ( m1_subset_1 @ ( sk_C_2 @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['85','109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ X0 )
        | ( m1_subset_1 @ ( sk_C_2 @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C_2 @ X0 @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) ) @ sk_B )
        | ( r1_tarski @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ X0 ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X13 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X13 @ X11 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('114',plain,
    ( ( ( r1_tarski @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_B ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( r1_tarski @ ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_B )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) )
      = sk_B )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['63','115'])).

thf('117',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('118',plain,
    ( ! [X35: $i] :
        ( ( sk_B
         != ( k5_waybel_0 @ sk_A @ X35 ) )
        | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ( sk_B
         != ( k5_waybel_0 @ sk_A @ X35 ) )
        | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('119',plain,
    ( ( sk_B
     != ( k5_waybel_0 @ sk_A @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( ( v14_waybel_0 @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ( sk_B
           != ( k5_waybel_0 @ sk_A @ X35 ) )
          | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( sk_B != sk_B )
   <= ( ( v14_waybel_0 @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ( sk_B
           != ( k5_waybel_0 @ sk_A @ X35 ) )
          | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,
    ( ~ ! [X35: $i] :
          ( ( sk_B
           != ( k5_waybel_0 @ sk_A @ X35 ) )
          | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( sk_B
      = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
    | ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('123',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('124',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( r2_hidden @ ( sk_D_1 @ X14 @ X16 @ X15 ) @ X16 )
      | ( r2_lattice3 @ X15 @ X16 @ X14 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('125',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ sk_C_3 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C_3 @ X0 @ sk_A ) @ X0 ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ sk_A @ X0 @ sk_C_3 )
        | ( r2_hidden @ ( sk_D_1 @ sk_C_3 @ X0 @ sk_A ) @ X0 ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('129',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X14 @ X16 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ( r2_lattice3 @ X15 @ X16 @ X14 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('130',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ sk_C_3 )
        | ( m1_subset_1 @ ( sk_D_1 @ sk_C_3 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ sk_A @ X0 @ sk_C_3 )
        | ( m1_subset_1 @ ( sk_D_1 @ sk_C_3 @ X0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( sk_B
      = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
   <= ( sk_B
      = ( k5_waybel_0 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('134',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('135',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r2_hidden @ X28 @ ( k5_waybel_0 @ X27 @ X26 ) )
      | ( r1_orders_2 @ X27 @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('136',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X0 @ sk_C_3 )
        | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_C_3 ) ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r1_orders_2 @ sk_A @ X0 @ sk_C_3 )
        | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_C_3 ) ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r1_orders_2 @ sk_A @ X0 @ sk_C_3 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ( sk_B
        = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
      & ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['133','138'])).

thf('140',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ sk_A @ X0 @ sk_C_3 )
        | ( v2_struct_0 @ sk_A )
        | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C_3 @ X0 @ sk_A ) @ sk_C_3 )
        | ~ ( r2_hidden @ ( sk_D_1 @ sk_C_3 @ X0 @ sk_A ) @ sk_B ) )
   <= ( ( sk_B
        = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
      & ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['132','139'])).

thf('141',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_C_3 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C_3 @ sk_B @ sk_A ) @ sk_C_3 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_C_3 ) )
   <= ( ( sk_B
        = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
      & ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['127','140'])).

thf('142',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C_3 @ sk_B @ sk_A ) @ sk_C_3 )
      | ( r2_lattice3 @ sk_A @ sk_B @ sk_C_3 ) )
   <= ( ( sk_B
        = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
      & ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( ( r2_lattice3 @ sk_A @ sk_B @ sk_C_3 )
      | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C_3 @ sk_B @ sk_A ) @ sk_C_3 ) )
   <= ( ( sk_B
        = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
      & ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('146',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_orders_2 @ X15 @ ( sk_D_1 @ X14 @ X16 @ X15 ) @ X14 )
      | ( r2_lattice3 @ X15 @ X16 @ X14 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('147',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_orders_2 @ sk_A )
        | ( r2_lattice3 @ sk_A @ X0 @ sk_C_3 )
        | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C_3 @ X0 @ sk_A ) @ sk_C_3 ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ! [X0: $i] :
        ( ( r2_lattice3 @ sk_A @ X0 @ sk_C_3 )
        | ~ ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_C_3 @ X0 @ sk_A ) @ sk_C_3 ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ sk_C_3 )
   <= ( ( sk_B
        = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
      & ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['144','149'])).

thf('151',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('152',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( v1_waybel_0 @ X7 @ X8 )
      | ~ ( v12_waybel_0 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r2_lattice3 @ X8 @ X7 @ X9 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( v14_waybel_0 @ X7 @ X8 )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d21_waybel_0])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v14_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ X0 )
      | ~ ( v12_waybel_0 @ sk_B @ sk_A )
      | ~ ( v1_waybel_0 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v14_waybel_0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155','156','157','158','159'])).

thf('161',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ sk_C_3 )
      | ~ ( r2_hidden @ sk_C_3 @ sk_B )
      | ( v14_waybel_0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['151','160'])).

thf('162',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v14_waybel_0 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ sk_C_3 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( sk_B
        = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
      & ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['150','161'])).

thf('163',plain,
    ( ( sk_B
      = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
   <= ( sk_B
      = ( k5_waybel_0 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('164',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('165',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('166',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r1_orders_2 @ X27 @ X28 @ X26 )
      | ( r2_hidden @ X28 @ ( k5_waybel_0 @ X27 @ X26 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t17_waybel_0])).

thf('167',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C_3 ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ sk_C_3 ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( ~ ( r1_orders_2 @ sk_A @ sk_C_3 @ sk_C_3 )
      | ( r2_hidden @ sk_C_3 @ ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['164','169'])).

thf('171',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('172',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(reflexivity_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_orders_2 @ A @ B @ B ) ) )).

thf('173',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r3_orders_2 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('174',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A )
        | ( r3_orders_2 @ sk_A @ sk_C_3 @ sk_C_3 ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r3_orders_2 @ sk_A @ sk_C_3 @ sk_C_3 ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ! [X0: $i] :
        ( ( r3_orders_2 @ sk_A @ sk_C_3 @ sk_C_3 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( r3_orders_2 @ sk_A @ sk_C_3 @ sk_C_3 )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['171','179'])).

thf('181',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('182',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( r1_orders_2 @ X21 @ X20 @ X22 )
      | ~ ( r3_orders_2 @ X21 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('183',plain,
    ( ! [X0: $i] :
        ( ~ ( r3_orders_2 @ sk_A @ sk_C_3 @ X0 )
        | ( r1_orders_2 @ sk_A @ sk_C_3 @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v3_orders_2 @ sk_A )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ! [X0: $i] :
        ( ~ ( r3_orders_2 @ sk_A @ sk_C_3 @ X0 )
        | ( r1_orders_2 @ sk_A @ sk_C_3 @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C_3 @ sk_C_3 ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['180','186'])).

thf('188',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('189',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ sk_C_3 @ sk_C_3 ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C_3 @ sk_C_3 )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( ( r2_hidden @ sk_C_3 @ ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['170','191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( r2_hidden @ sk_C_3 @ ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
   <= ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( r2_hidden @ sk_C_3 @ sk_B )
   <= ( ( sk_B
        = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
      & ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['163','194'])).

thf('196',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v14_waybel_0 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( sk_B
        = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
      & ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['162','195'])).

thf('197',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v14_waybel_0 @ sk_B @ sk_A ) )
   <= ( ( sk_B
        = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
      & ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['196','197'])).

thf('199',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( v14_waybel_0 @ sk_B @ sk_A )
   <= ( ( sk_B
        = ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
      & ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,
    ( ~ ( v14_waybel_0 @ sk_B @ sk_A )
   <= ~ ( v14_waybel_0 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('202',plain,
    ( ( sk_B
     != ( k5_waybel_0 @ sk_A @ sk_C_3 ) )
    | ( v14_waybel_0 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','121','122','202'])).


%------------------------------------------------------------------------------
