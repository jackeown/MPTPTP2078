%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QpDdIVOrTw

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 (1020 expanded)
%              Number of leaves         :   33 ( 314 expanded)
%              Depth                    :   16
%              Number of atoms          : 1016 (16113 expanded)
%              Number of equality atoms :   29 ( 618 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(k7_lattice3_type,type,(
    k7_lattice3: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(a_2_0_yellow_6_type,type,(
    a_2_0_yellow_6: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t38_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
             => ? [D: $i] :
                  ( ( v3_pre_topc @ D @ A )
                  & ( r2_hidden @ B @ D )
                  & ( D = C )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
               => ? [D: $i] :
                    ( ( v3_pre_topc @ D @ A )
                    & ( r2_hidden @ B @ D )
                    & ( D = C )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_yellow_6])).

thf('0',plain,(
    ! [X20: $i] :
      ( ~ ( v3_pre_topc @ X20 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X20 )
      | ( X20 != sk_C )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['0'])).

thf('2',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d17_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k9_yellow_6 @ A @ B )
            = ( k7_lattice3 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ A @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( ( k9_yellow_6 @ X10 @ X9 )
        = ( k7_lattice3 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ X10 @ X9 ) ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d17_yellow_6])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k9_yellow_6 @ sk_A @ sk_B )
      = ( k7_lattice3 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k9_yellow_6 @ sk_A @ sk_B )
      = ( k7_lattice3 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k9_yellow_6 @ sk_A @ sk_B )
    = ( k7_lattice3 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t12_yellow_6,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( u1_struct_0 @ A )
        = ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X19: $i] :
      ( ( ( u1_struct_0 @ X19 )
        = ( u1_struct_0 @ ( k7_lattice3 @ X19 ) ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow_6])).

thf('15',plain,
    ( ( ( u1_struct_0 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) )
      = ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('16',plain,(
    ! [X7: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X6: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('18',plain,
    ( ( a_2_0_yellow_6 @ sk_A @ sk_B )
    = ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( a_2_0_yellow_6 @ sk_A @ sk_B )
    = ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_2_0_yellow_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( ( r2_hidden @ A @ ( a_2_0_yellow_6 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( v3_pre_topc @ D @ B )
            & ( r2_hidden @ C @ D )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( v3_pre_topc @ ( sk_D @ X16 @ X15 @ X17 ) @ X15 )
      | ~ ( r2_hidden @ X17 @ ( a_2_0_yellow_6 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_yellow_6])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( sk_D @ sk_B @ sk_A @ X0 ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( sk_D @ sk_B @ sk_A @ X0 ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_D @ sk_B @ sk_A @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ ( sk_D @ sk_B @ sk_A @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,
    ( ( k9_yellow_6 @ sk_A @ sk_B )
    = ( k7_lattice3 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('31',plain,(
    ! [X7: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('32',plain,(
    ! [X19: $i] :
      ( ( ( u1_struct_0 @ X19 )
        = ( u1_struct_0 @ ( k7_lattice3 @ X19 ) ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow_6])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ ( k7_lattice3 @ X0 ) )
      | ~ ( l1_struct_0 @ ( k7_lattice3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_struct_0 @ ( k7_lattice3 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k7_lattice3 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X6: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_struct_0 @ ( k7_lattice3 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k7_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( l1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k7_lattice3 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,
    ( ( k9_yellow_6 @ sk_A @ sk_B )
    = ( k7_lattice3 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('40',plain,
    ( ~ ( l1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc20_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ~ ( v2_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( v2_struct_0 @ ( k9_yellow_6 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc20_yellow_6])).

thf('43',plain,
    ( ~ ( v2_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v2_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ( v2_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['40','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( l1_orders_2 @ ( k9_yellow_6 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( l1_orders_2 @ ( k9_yellow_6 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_yellow_6])).

thf('52',plain,
    ( ( l1_orders_2 @ ( k9_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( l1_orders_2 @ ( k9_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_orders_2 @ ( k9_yellow_6 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['55','56'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('58',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('59',plain,(
    l1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','59'])).

thf('61',plain,(
    v3_pre_topc @ ( sk_D @ sk_B @ sk_A @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['29','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','18','19'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( X17
        = ( sk_D @ X16 @ X15 @ X17 ) )
      | ~ ( r2_hidden @ X17 @ ( a_2_0_yellow_6 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_yellow_6])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
      | ( X0
        = ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
      | ( X0
        = ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
    | ( sk_C
      = ( sk_D @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','59'])).

thf('73',plain,
    ( sk_C
    = ( sk_D @ sk_B @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['61','73'])).

thf('75',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('76',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','18','19'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( r2_hidden @ X16 @ ( sk_D @ X16 @ X15 @ X17 ) )
      | ~ ( r2_hidden @ X17 @ ( a_2_0_yellow_6 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_yellow_6])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( sk_D @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','85'])).

thf('87',plain,
    ( sk_C
    = ( sk_D @ sk_B @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','59'])).

thf('90',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['1'])).

thf('92',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('94',plain,(
    ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['76','92','93'])).

thf('95',plain,(
    ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['2','94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','18','19'])).

thf('97',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ ( sk_D @ X16 @ X15 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X17 @ ( a_2_0_yellow_6 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_yellow_6])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( sk_C
    = ( sk_D @ sk_B @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('104',plain,(
    ~ ( v1_xboole_0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','59'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['95','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QpDdIVOrTw
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:50:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 107 iterations in 0.051s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(k9_yellow_6_type, type, k9_yellow_6: $i > $i > $i).
% 0.20/0.51  thf(k7_lattice3_type, type, k7_lattice3: $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.51  thf(a_2_0_yellow_6_type, type, a_2_0_yellow_6: $i > $i > $i).
% 0.20/0.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.20/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(t38_yellow_6, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 0.20/0.51               ( ?[D:$i]:
% 0.20/0.51                 ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) & 
% 0.20/0.51                   ( ( D ) = ( C ) ) & 
% 0.20/0.51                   ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51            ( l1_pre_topc @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) =>
% 0.20/0.51                  ( ?[D:$i]:
% 0.20/0.51                    ( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) & 
% 0.20/0.51                      ( ( D ) = ( C ) ) & 
% 0.20/0.51                      ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t38_yellow_6])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X20 : $i]:
% 0.20/0.51         (~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.51          | ~ (r2_hidden @ sk_B @ X20)
% 0.20/0.51          | ((X20) != (sk_C))
% 0.20/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | ~ (r2_hidden @ sk_B @ sk_C)
% 0.20/0.51        | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.20/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.51         <= (~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.51      inference('split', [status(esa)], ['1'])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d2_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (v1_xboole_0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 0.20/0.51        | (r2_hidden @ sk_C @ (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('6', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d17_yellow_6, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51           ( ( k9_yellow_6 @ A @ B ) =
% 0.20/0.51             ( k7_lattice3 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.20/0.51          | ((k9_yellow_6 @ X10 @ X9)
% 0.20/0.51              = (k7_lattice3 @ (k2_yellow_1 @ (a_2_0_yellow_6 @ X10 @ X9))))
% 0.20/0.51          | ~ (l1_pre_topc @ X10)
% 0.20/0.51          | ~ (v2_pre_topc @ X10)
% 0.20/0.51          | (v2_struct_0 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [d17_yellow_6])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ((k9_yellow_6 @ sk_A @ sk_B)
% 0.20/0.51            = (k7_lattice3 @ (k2_yellow_1 @ (a_2_0_yellow_6 @ sk_A @ sk_B)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k9_yellow_6 @ sk_A @ sk_B)
% 0.20/0.51            = (k7_lattice3 @ (k2_yellow_1 @ (a_2_0_yellow_6 @ sk_A @ sk_B)))))),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.51  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (((k9_yellow_6 @ sk_A @ sk_B)
% 0.20/0.51         = (k7_lattice3 @ (k2_yellow_1 @ (a_2_0_yellow_6 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf(t12_yellow_6, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_orders_2 @ A ) =>
% 0.20/0.51       ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X19 : $i]:
% 0.20/0.51         (((u1_struct_0 @ X19) = (u1_struct_0 @ (k7_lattice3 @ X19)))
% 0.20/0.51          | ~ (l1_orders_2 @ X19))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_yellow_6])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((((u1_struct_0 @ (k2_yellow_1 @ (a_2_0_yellow_6 @ sk_A @ sk_B)))
% 0.20/0.51          = (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))
% 0.20/0.51        | ~ (l1_orders_2 @ (k2_yellow_1 @ (a_2_0_yellow_6 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf(t1_yellow_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.51       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.51  thf('16', plain, (![X7 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X7)) = (X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.51  thf(dt_k2_yellow_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.20/0.51       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.20/0.51  thf('17', plain, (![X6 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (((a_2_0_yellow_6 @ sk_A @ sk_B)
% 0.20/0.51         = (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (((a_2_0_yellow_6 @ sk_A @ sk_B)
% 0.20/0.51         = (u1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (((v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | (r2_hidden @ sk_C @ (a_2_0_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['5', '18', '19'])).
% 0.20/0.51  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(fraenkel_a_2_0_yellow_6, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51         ( l1_pre_topc @ B ) & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.51       ( ( r2_hidden @ A @ ( a_2_0_yellow_6 @ B @ C ) ) <=>
% 0.20/0.51         ( ?[D:$i]:
% 0.20/0.51           ( ( v3_pre_topc @ D @ B ) & ( r2_hidden @ C @ D ) & 
% 0.20/0.51             ( ( A ) = ( D ) ) & 
% 0.20/0.51             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X15)
% 0.20/0.51          | ~ (v2_pre_topc @ X15)
% 0.20/0.51          | (v2_struct_0 @ X15)
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.20/0.51          | (v3_pre_topc @ (sk_D @ X16 @ X15 @ X17) @ X15)
% 0.20/0.51          | ~ (r2_hidden @ X17 @ (a_2_0_yellow_6 @ X15 @ X16)))),
% 0.20/0.51      inference('cnf', [status(esa)], [fraenkel_a_2_0_yellow_6])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51          | (v3_pre_topc @ (sk_D @ sk_B @ sk_A @ X0) @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51          | (v3_pre_topc @ (sk_D @ sk_B @ sk_A @ X0) @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.51  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v3_pre_topc @ (sk_D @ sk_B @ sk_A @ X0) @ sk_A)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (a_2_0_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (((v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | (v3_pre_topc @ (sk_D @ sk_B @ sk_A @ sk_C) @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (((k9_yellow_6 @ sk_A @ sk_B)
% 0.20/0.51         = (k7_lattice3 @ (k2_yellow_1 @ (a_2_0_yellow_6 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('31', plain, (![X7 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X7)) = (X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X19 : $i]:
% 0.20/0.51         (((u1_struct_0 @ X19) = (u1_struct_0 @ (k7_lattice3 @ X19)))
% 0.20/0.51          | ~ (l1_orders_2 @ X19))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_yellow_6])).
% 0.20/0.51  thf(fc2_struct_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.51       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X3 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 0.20/0.51          | ~ (l1_struct_0 @ X3)
% 0.20/0.51          | (v2_struct_0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (l1_orders_2 @ X0)
% 0.20/0.51          | (v2_struct_0 @ (k7_lattice3 @ X0))
% 0.20/0.51          | ~ (l1_struct_0 @ (k7_lattice3 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ X0)
% 0.20/0.51          | ~ (l1_struct_0 @ (k7_lattice3 @ (k2_yellow_1 @ X0)))
% 0.20/0.51          | (v2_struct_0 @ (k7_lattice3 @ (k2_yellow_1 @ X0)))
% 0.20/0.51          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '34'])).
% 0.20/0.51  thf('36', plain, (![X6 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ X0)
% 0.20/0.51          | ~ (l1_struct_0 @ (k7_lattice3 @ (k2_yellow_1 @ X0)))
% 0.20/0.51          | (v2_struct_0 @ (k7_lattice3 @ (k2_yellow_1 @ X0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((~ (l1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | (v2_struct_0 @ 
% 0.20/0.51           (k7_lattice3 @ (k2_yellow_1 @ (a_2_0_yellow_6 @ sk_A @ sk_B))))
% 0.20/0.51        | ~ (v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (((k9_yellow_6 @ sk_A @ sk_B)
% 0.20/0.51         = (k7_lattice3 @ (k2_yellow_1 @ (a_2_0_yellow_6 @ sk_A @ sk_B))))),
% 0.20/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((~ (l1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | (v2_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | ~ (v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(fc20_yellow_6, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51       ( ~( v2_struct_0 @ ( k9_yellow_6 @ A @ B ) ) ) ))).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X13)
% 0.20/0.51          | ~ (v2_pre_topc @ X13)
% 0.20/0.51          | (v2_struct_0 @ X13)
% 0.20/0.51          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.20/0.51          | ~ (v2_struct_0 @ (k9_yellow_6 @ X13 @ X14)))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc20_yellow_6])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((~ (v2_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      ((~ (v2_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.51  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('48', plain, (~ (v2_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      ((~ (v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | ~ (l1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('clc', [status(thm)], ['40', '48'])).
% 0.20/0.51  thf('50', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k9_yellow_6, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51       ( l1_orders_2 @ ( k9_yellow_6 @ A @ B ) ) ))).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X11)
% 0.20/0.51          | ~ (v2_pre_topc @ X11)
% 0.20/0.51          | (v2_struct_0 @ X11)
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.20/0.51          | (l1_orders_2 @ (k9_yellow_6 @ X11 @ X12)))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k9_yellow_6])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (((l1_orders_2 @ (k9_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (((l1_orders_2 @ (k9_yellow_6 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.20/0.51  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('57', plain, ((l1_orders_2 @ (k9_yellow_6 @ sk_A @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['55', '56'])).
% 0.20/0.51  thf(dt_l1_orders_2, axiom,
% 0.20/0.51    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.51  thf('58', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_orders_2 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.20/0.51  thf('59', plain, ((l1_struct_0 @ (k9_yellow_6 @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.51  thf('60', plain, (~ (v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['49', '59'])).
% 0.20/0.51  thf('61', plain, ((v3_pre_topc @ (sk_D @ sk_B @ sk_A @ sk_C) @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['29', '60'])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (((v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | (r2_hidden @ sk_C @ (a_2_0_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['5', '18', '19'])).
% 0.20/0.51  thf('63', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X15)
% 0.20/0.51          | ~ (v2_pre_topc @ X15)
% 0.20/0.51          | (v2_struct_0 @ X15)
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.20/0.51          | ((X17) = (sk_D @ X16 @ X15 @ X17))
% 0.20/0.51          | ~ (r2_hidden @ X17 @ (a_2_0_yellow_6 @ X15 @ X16)))),
% 0.20/0.51      inference('cnf', [status(esa)], [fraenkel_a_2_0_yellow_6])).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51          | ((X0) = (sk_D @ sk_B @ sk_A @ X0))
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.51  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51          | ((X0) = (sk_D @ sk_B @ sk_A @ X0))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.20/0.51  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((X0) = (sk_D @ sk_B @ sk_A @ X0))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (a_2_0_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      (((v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | ((sk_C) = (sk_D @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['62', '70'])).
% 0.20/0.51  thf('72', plain, (~ (v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['49', '59'])).
% 0.20/0.51  thf('73', plain, (((sk_C) = (sk_D @ sk_B @ sk_A @ sk_C))),
% 0.20/0.51      inference('clc', [status(thm)], ['71', '72'])).
% 0.20/0.51  thf('74', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['61', '73'])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['1'])).
% 0.20/0.51  thf('76', plain, (((v3_pre_topc @ sk_C @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      (((v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | (r2_hidden @ sk_C @ (a_2_0_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['5', '18', '19'])).
% 0.20/0.51  thf('78', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X15)
% 0.20/0.51          | ~ (v2_pre_topc @ X15)
% 0.20/0.51          | (v2_struct_0 @ X15)
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.20/0.51          | (r2_hidden @ X16 @ (sk_D @ X16 @ X15 @ X17))
% 0.20/0.51          | ~ (r2_hidden @ X17 @ (a_2_0_yellow_6 @ X15 @ X16)))),
% 0.20/0.51      inference('cnf', [status(esa)], [fraenkel_a_2_0_yellow_6])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51          | (r2_hidden @ sk_B @ (sk_D @ sk_B @ sk_A @ X0))
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.51  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('83', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51          | (r2_hidden @ sk_B @ (sk_D @ sk_B @ sk_A @ X0))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.20/0.51  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ sk_B @ (sk_D @ sk_B @ sk_A @ X0))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (a_2_0_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('clc', [status(thm)], ['83', '84'])).
% 0.20/0.51  thf('86', plain,
% 0.20/0.51      (((v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | (r2_hidden @ sk_B @ (sk_D @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['77', '85'])).
% 0.20/0.51  thf('87', plain, (((sk_C) = (sk_D @ sk_B @ sk_A @ sk_C))),
% 0.20/0.51      inference('clc', [status(thm)], ['71', '72'])).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      (((v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | (r2_hidden @ sk_B @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['86', '87'])).
% 0.20/0.51  thf('89', plain, (~ (v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['49', '59'])).
% 0.20/0.51  thf('90', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.20/0.51      inference('clc', [status(thm)], ['88', '89'])).
% 0.20/0.51  thf('91', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 0.20/0.51      inference('split', [status(esa)], ['1'])).
% 0.20/0.51  thf('92', plain, (((r2_hidden @ sk_B @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['90', '91'])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      (~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_B @ sk_C)) | ~ ((v3_pre_topc @ sk_C @ sk_A))),
% 0.20/0.51      inference('split', [status(esa)], ['1'])).
% 0.20/0.51  thf('94', plain,
% 0.20/0.51      (~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['76', '92', '93'])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      (~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['2', '94'])).
% 0.20/0.51  thf('96', plain,
% 0.20/0.51      (((v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | (r2_hidden @ sk_C @ (a_2_0_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['5', '18', '19'])).
% 0.20/0.51  thf('97', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (l1_pre_topc @ X15)
% 0.20/0.51          | ~ (v2_pre_topc @ X15)
% 0.20/0.51          | (v2_struct_0 @ X15)
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.20/0.51          | (m1_subset_1 @ (sk_D @ X16 @ X15 @ X17) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.51          | ~ (r2_hidden @ X17 @ (a_2_0_yellow_6 @ X15 @ X16)))),
% 0.20/0.51      inference('cnf', [status(esa)], [fraenkel_a_2_0_yellow_6])).
% 0.20/0.51  thf('98', plain,
% 0.20/0.51      (((v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | (m1_subset_1 @ (sk_D @ sk_B @ sk_A @ sk_C) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['96', '97'])).
% 0.20/0.51  thf('99', plain, (((sk_C) = (sk_D @ sk_B @ sk_A @ sk_C))),
% 0.20/0.51      inference('clc', [status(thm)], ['71', '72'])).
% 0.20/0.51  thf('100', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('103', plain,
% 0.20/0.51      (((v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))
% 0.20/0.51        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 0.20/0.51  thf('104', plain, (~ (v1_xboole_0 @ (a_2_0_yellow_6 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['49', '59'])).
% 0.20/0.51  thf('105', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('clc', [status(thm)], ['103', '104'])).
% 0.20/0.51  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('107', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('clc', [status(thm)], ['105', '106'])).
% 0.20/0.51  thf('108', plain, ($false), inference('demod', [status(thm)], ['95', '107'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
