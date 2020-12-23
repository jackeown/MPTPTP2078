%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CHQLP0QRab

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:44 EST 2020

% Result     : Theorem 4.57s
% Output     : Refutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 362 expanded)
%              Number of leaves         :   27 ( 112 expanded)
%              Depth                    :   19
%              Number of atoms          : 1993 (5184 expanded)
%              Number of equality atoms :   28 (  96 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t33_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_compts_1 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v2_compts_1 @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_compts_1 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
          <=> ( ( v2_compts_1 @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_compts_1])).

thf('0',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X9 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('6',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X9 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( g1_pre_topc @ X12 @ X13 )
       != ( g1_pre_topc @ X10 @ X11 ) )
      | ( X12 = X10 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X9 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['11','14'])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','20'])).

thf('22',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('23',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('27',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('29',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X15 @ X14 ) )
        = X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X5 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( m1_pre_topc @ X17 @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['37','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['11','14'])).

thf(t28_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( C = D )
                   => ( ( v2_compts_1 @ C @ A )
                    <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_compts_1 @ X21 @ X19 )
      | ( v2_compts_1 @ X20 @ X18 )
      | ( X21 != X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_compts_1])).

thf('45',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_compts_1 @ X20 @ X18 )
      | ~ ( v2_compts_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_pre_topc @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v2_compts_1 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v2_compts_1 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v2_compts_1 @ X1 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_compts_1 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( v2_compts_1 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v2_compts_1 @ X1 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v2_compts_1 @ X1 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_compts_1 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_compts_1 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v2_compts_1 @ X1 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ X1 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_compts_1 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_compts_1 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v2_compts_1 @ X1 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_compts_1 @ X20 @ X18 )
      | ( v2_compts_1 @ X21 @ X19 )
      | ( X21 != X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_compts_1])).

thf('62',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_compts_1 @ X20 @ X19 )
      | ~ ( v2_compts_1 @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_pre_topc @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ X0 )
        | ( v2_compts_1 @ sk_B @ sk_A )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ X0 )
        | ( v2_compts_1 @ sk_B @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_compts_1 @ sk_B @ sk_A )
        | ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,
    ( ( ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
      | ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
      | ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ sk_B @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( v2_compts_1 @ sk_B @ sk_A )
      | ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','72'])).

thf('74',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
   <= ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('75',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['11','14'])).

thf('79',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,
    ( ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['78','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('85',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('87',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('89',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['24'])).

thf('90',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_compts_1 @ X20 @ X18 )
      | ~ ( v2_compts_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_pre_topc @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ sk_A )
        | ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( v2_compts_1 @ sk_B @ sk_A )
        | ( v2_compts_1 @ sk_B @ X0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ sk_A )
        | ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['88','95'])).

thf('97',plain,
    ( ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['87','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['86','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['37','41'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['11','14'])).

thf('108',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_compts_1 @ X20 @ X19 )
      | ~ ( v2_compts_1 @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_pre_topc @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v2_compts_1 @ X1 @ X2 )
      | ( v2_compts_1 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v2_compts_1 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_compts_1 @ X1 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( v2_compts_1 @ X1 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_compts_1 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v2_compts_1 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_compts_1 @ X1 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_compts_1 @ X1 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_compts_1 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_compts_1 @ X1 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['104','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_compts_1 @ X1 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_compts_1 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['103','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['102','118'])).

thf('120',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('121',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
    | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('123',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['21','22','75','77','85','121','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CHQLP0QRab
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:09:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.57/4.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.57/4.76  % Solved by: fo/fo7.sh
% 4.57/4.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.57/4.76  % done 2761 iterations in 4.302s
% 4.57/4.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.57/4.76  % SZS output start Refutation
% 4.57/4.76  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 4.57/4.76  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 4.57/4.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.57/4.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.57/4.76  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 4.57/4.76  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.57/4.76  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 4.57/4.76  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 4.57/4.76  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 4.57/4.76  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.57/4.76  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 4.57/4.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.57/4.76  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.57/4.76  thf(sk_A_type, type, sk_A: $i).
% 4.57/4.76  thf(sk_B_type, type, sk_B: $i).
% 4.57/4.76  thf(t33_compts_1, conjecture,
% 4.57/4.76    (![A:$i]:
% 4.57/4.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.57/4.76       ( ![B:$i]:
% 4.57/4.76         ( ( ( v2_compts_1 @ B @ A ) & 
% 4.57/4.76             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 4.57/4.76           ( ( v2_compts_1 @
% 4.57/4.76               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 4.57/4.76             ( m1_subset_1 @
% 4.57/4.76               B @ 
% 4.57/4.76               ( k1_zfmisc_1 @
% 4.57/4.76                 ( u1_struct_0 @
% 4.57/4.76                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 4.57/4.76  thf(zf_stmt_0, negated_conjecture,
% 4.57/4.76    (~( ![A:$i]:
% 4.57/4.76        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.57/4.76            ( l1_pre_topc @ A ) ) =>
% 4.57/4.76          ( ![B:$i]:
% 4.57/4.76            ( ( ( v2_compts_1 @ B @ A ) & 
% 4.57/4.76                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 4.57/4.76              ( ( v2_compts_1 @
% 4.57/4.76                  B @ 
% 4.57/4.76                  ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 4.57/4.76                ( m1_subset_1 @
% 4.57/4.76                  B @ 
% 4.57/4.76                  ( k1_zfmisc_1 @
% 4.57/4.76                    ( u1_struct_0 @
% 4.57/4.76                      ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) )),
% 4.57/4.76    inference('cnf.neg', [status(esa)], [t33_compts_1])).
% 4.57/4.76  thf('0', plain,
% 4.57/4.76      (((v2_compts_1 @ sk_B @ 
% 4.57/4.76         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.57/4.76        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('1', plain,
% 4.57/4.76      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('split', [status(esa)], ['0'])).
% 4.57/4.76  thf(dt_u1_pre_topc, axiom,
% 4.57/4.76    (![A:$i]:
% 4.57/4.76     ( ( l1_pre_topc @ A ) =>
% 4.57/4.76       ( m1_subset_1 @
% 4.57/4.76         ( u1_pre_topc @ A ) @ 
% 4.57/4.76         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 4.57/4.76  thf('2', plain,
% 4.57/4.76      (![X9 : $i]:
% 4.57/4.76         ((m1_subset_1 @ (u1_pre_topc @ X9) @ 
% 4.57/4.76           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 4.57/4.76          | ~ (l1_pre_topc @ X9))),
% 4.57/4.76      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 4.57/4.76  thf(dt_g1_pre_topc, axiom,
% 4.57/4.76    (![A:$i,B:$i]:
% 4.57/4.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 4.57/4.76       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 4.57/4.76         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 4.57/4.76  thf('3', plain,
% 4.57/4.76      (![X3 : $i, X4 : $i]:
% 4.57/4.76         ((v1_pre_topc @ (g1_pre_topc @ X3 @ X4))
% 4.57/4.76          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 4.57/4.76      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 4.57/4.76  thf('4', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | (v1_pre_topc @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['2', '3'])).
% 4.57/4.76  thf(abstractness_v1_pre_topc, axiom,
% 4.57/4.76    (![A:$i]:
% 4.57/4.76     ( ( l1_pre_topc @ A ) =>
% 4.57/4.76       ( ( v1_pre_topc @ A ) =>
% 4.57/4.76         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 4.57/4.76  thf('5', plain,
% 4.57/4.76      (![X2 : $i]:
% 4.57/4.76         (~ (v1_pre_topc @ X2)
% 4.57/4.76          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 4.57/4.76          | ~ (l1_pre_topc @ X2))),
% 4.57/4.76      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 4.57/4.76  thf('6', plain,
% 4.57/4.76      (![X9 : $i]:
% 4.57/4.76         ((m1_subset_1 @ (u1_pre_topc @ X9) @ 
% 4.57/4.76           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 4.57/4.76          | ~ (l1_pre_topc @ X9))),
% 4.57/4.76      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 4.57/4.76  thf(free_g1_pre_topc, axiom,
% 4.57/4.76    (![A:$i,B:$i]:
% 4.57/4.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 4.57/4.76       ( ![C:$i,D:$i]:
% 4.57/4.76         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 4.57/4.76           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 4.57/4.76  thf('7', plain,
% 4.57/4.76      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 4.57/4.76         (((g1_pre_topc @ X12 @ X13) != (g1_pre_topc @ X10 @ X11))
% 4.57/4.76          | ((X12) = (X10))
% 4.57/4.76          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 4.57/4.76      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 4.57/4.76  thf('8', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | ((u1_struct_0 @ X0) = (X1))
% 4.57/4.76          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 4.57/4.76              != (g1_pre_topc @ X1 @ X2)))),
% 4.57/4.76      inference('sup-', [status(thm)], ['6', '7'])).
% 4.57/4.76  thf('9', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.76         (((X0) != (g1_pre_topc @ X2 @ X1))
% 4.57/4.76          | ~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (v1_pre_topc @ X0)
% 4.57/4.76          | ((u1_struct_0 @ X0) = (X2))
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('sup-', [status(thm)], ['5', '8'])).
% 4.57/4.76  thf('10', plain,
% 4.57/4.76      (![X1 : $i, X2 : $i]:
% 4.57/4.76         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 4.57/4.76          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 4.57/4.76          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 4.57/4.76      inference('simplify', [status(thm)], ['9'])).
% 4.57/4.76  thf('11', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (l1_pre_topc @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ((u1_struct_0 @ 
% 4.57/4.76              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76              = (u1_struct_0 @ X0)))),
% 4.57/4.76      inference('sup-', [status(thm)], ['4', '10'])).
% 4.57/4.76  thf('12', plain,
% 4.57/4.76      (![X9 : $i]:
% 4.57/4.76         ((m1_subset_1 @ (u1_pre_topc @ X9) @ 
% 4.57/4.76           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 4.57/4.76          | ~ (l1_pre_topc @ X9))),
% 4.57/4.76      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 4.57/4.76  thf('13', plain,
% 4.57/4.76      (![X3 : $i, X4 : $i]:
% 4.57/4.76         ((l1_pre_topc @ (g1_pre_topc @ X3 @ X4))
% 4.57/4.76          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 4.57/4.76      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 4.57/4.76  thf('14', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | (l1_pre_topc @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['12', '13'])).
% 4.57/4.76  thf('15', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (((u1_struct_0 @ 
% 4.57/4.76            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76            = (u1_struct_0 @ X0))
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('clc', [status(thm)], ['11', '14'])).
% 4.57/4.76  thf('16', plain,
% 4.57/4.76      ((~ (m1_subset_1 @ sk_B @ 
% 4.57/4.76           (k1_zfmisc_1 @ 
% 4.57/4.76            (u1_struct_0 @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 4.57/4.76        | ~ (v2_compts_1 @ sk_B @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.57/4.76        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.57/4.76        | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('17', plain,
% 4.57/4.76      ((~ (m1_subset_1 @ sk_B @ 
% 4.57/4.76           (k1_zfmisc_1 @ 
% 4.57/4.76            (u1_struct_0 @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 4.57/4.76         <= (~
% 4.57/4.76             ((m1_subset_1 @ sk_B @ 
% 4.57/4.76               (k1_zfmisc_1 @ 
% 4.57/4.76                (u1_struct_0 @ 
% 4.57/4.76                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 4.57/4.76      inference('split', [status(esa)], ['16'])).
% 4.57/4.76  thf('18', plain,
% 4.57/4.76      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.57/4.76         | ~ (l1_pre_topc @ sk_A)))
% 4.57/4.76         <= (~
% 4.57/4.76             ((m1_subset_1 @ sk_B @ 
% 4.57/4.76               (k1_zfmisc_1 @ 
% 4.57/4.76                (u1_struct_0 @ 
% 4.57/4.76                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['15', '17'])).
% 4.57/4.76  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('20', plain,
% 4.57/4.76      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.57/4.76         <= (~
% 4.57/4.76             ((m1_subset_1 @ sk_B @ 
% 4.57/4.76               (k1_zfmisc_1 @ 
% 4.57/4.76                (u1_struct_0 @ 
% 4.57/4.76                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 4.57/4.76      inference('demod', [status(thm)], ['18', '19'])).
% 4.57/4.76  thf('21', plain,
% 4.57/4.76      (((m1_subset_1 @ sk_B @ 
% 4.57/4.76         (k1_zfmisc_1 @ 
% 4.57/4.76          (u1_struct_0 @ 
% 4.57/4.76           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))) | 
% 4.57/4.76       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['1', '20'])).
% 4.57/4.76  thf('22', plain,
% 4.57/4.76      (~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 4.57/4.76       ~
% 4.57/4.76       ((v2_compts_1 @ sk_B @ 
% 4.57/4.76         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 4.57/4.76       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 4.57/4.76       ~
% 4.57/4.76       ((m1_subset_1 @ sk_B @ 
% 4.57/4.76         (k1_zfmisc_1 @ 
% 4.57/4.76          (u1_struct_0 @ 
% 4.57/4.76           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 4.57/4.76      inference('split', [status(esa)], ['16'])).
% 4.57/4.76  thf('23', plain,
% 4.57/4.76      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('split', [status(esa)], ['0'])).
% 4.57/4.76  thf('24', plain,
% 4.57/4.76      (((v2_compts_1 @ sk_B @ 
% 4.57/4.76         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.57/4.76        | (v2_compts_1 @ sk_B @ sk_A))),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('25', plain,
% 4.57/4.76      (((v2_compts_1 @ sk_B @ 
% 4.57/4.76         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 4.57/4.76         <= (((v2_compts_1 @ sk_B @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 4.57/4.76      inference('split', [status(esa)], ['24'])).
% 4.57/4.76  thf('26', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | (l1_pre_topc @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['12', '13'])).
% 4.57/4.76  thf(dt_k2_subset_1, axiom,
% 4.57/4.76    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 4.57/4.76  thf('27', plain,
% 4.57/4.76      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 4.57/4.76      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 4.57/4.76  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 4.57/4.76  thf('28', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 4.57/4.76      inference('cnf', [status(esa)], [d4_subset_1])).
% 4.57/4.76  thf('29', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 4.57/4.76      inference('demod', [status(thm)], ['27', '28'])).
% 4.57/4.76  thf(t29_pre_topc, axiom,
% 4.57/4.76    (![A:$i]:
% 4.57/4.76     ( ( l1_pre_topc @ A ) =>
% 4.57/4.76       ( ![B:$i]:
% 4.57/4.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.57/4.76           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 4.57/4.76  thf('30', plain,
% 4.57/4.76      (![X14 : $i, X15 : $i]:
% 4.57/4.76         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 4.57/4.76          | ((u1_struct_0 @ (k1_pre_topc @ X15 @ X14)) = (X14))
% 4.57/4.76          | ~ (l1_pre_topc @ X15))),
% 4.57/4.76      inference('cnf', [status(esa)], [t29_pre_topc])).
% 4.57/4.76  thf('31', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76              = (u1_struct_0 @ X0)))),
% 4.57/4.76      inference('sup-', [status(thm)], ['29', '30'])).
% 4.57/4.76  thf('32', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 4.57/4.76      inference('demod', [status(thm)], ['27', '28'])).
% 4.57/4.76  thf(dt_k1_pre_topc, axiom,
% 4.57/4.76    (![A:$i,B:$i]:
% 4.57/4.76     ( ( ( l1_pre_topc @ A ) & 
% 4.57/4.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.57/4.76       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 4.57/4.76         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 4.57/4.76  thf('33', plain,
% 4.57/4.76      (![X5 : $i, X6 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X5)
% 4.57/4.76          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 4.57/4.76          | (m1_pre_topc @ (k1_pre_topc @ X5 @ X6) @ X5))),
% 4.57/4.76      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 4.57/4.76  thf('34', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('sup-', [status(thm)], ['32', '33'])).
% 4.57/4.76  thf(t65_pre_topc, axiom,
% 4.57/4.76    (![A:$i]:
% 4.57/4.76     ( ( l1_pre_topc @ A ) =>
% 4.57/4.76       ( ![B:$i]:
% 4.57/4.76         ( ( l1_pre_topc @ B ) =>
% 4.57/4.76           ( ( m1_pre_topc @ A @ B ) <=>
% 4.57/4.76             ( m1_pre_topc @
% 4.57/4.76               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 4.57/4.76  thf('35', plain,
% 4.57/4.76      (![X16 : $i, X17 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X16)
% 4.57/4.76          | ~ (m1_pre_topc @ X17 @ X16)
% 4.57/4.76          | (m1_pre_topc @ X17 @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 4.57/4.76          | ~ (l1_pre_topc @ X17))),
% 4.57/4.76      inference('cnf', [status(esa)], [t65_pre_topc])).
% 4.57/4.76  thf('36', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('sup-', [status(thm)], ['34', '35'])).
% 4.57/4.76  thf('37', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 4.57/4.76           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('simplify', [status(thm)], ['36'])).
% 4.57/4.76  thf('38', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('sup-', [status(thm)], ['32', '33'])).
% 4.57/4.76  thf(dt_m1_pre_topc, axiom,
% 4.57/4.76    (![A:$i]:
% 4.57/4.76     ( ( l1_pre_topc @ A ) =>
% 4.57/4.76       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 4.57/4.76  thf('39', plain,
% 4.57/4.76      (![X7 : $i, X8 : $i]:
% 4.57/4.76         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 4.57/4.76      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 4.57/4.76  thf('40', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (l1_pre_topc @ X0)
% 4.57/4.76          | (l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['38', '39'])).
% 4.57/4.76  thf('41', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('simplify', [status(thm)], ['40'])).
% 4.57/4.76  thf('42', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.57/4.76      inference('clc', [status(thm)], ['37', '41'])).
% 4.57/4.76  thf('43', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (((u1_struct_0 @ 
% 4.57/4.76            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76            = (u1_struct_0 @ X0))
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('clc', [status(thm)], ['11', '14'])).
% 4.57/4.76  thf(t28_compts_1, axiom,
% 4.57/4.76    (![A:$i]:
% 4.57/4.76     ( ( l1_pre_topc @ A ) =>
% 4.57/4.76       ( ![B:$i]:
% 4.57/4.76         ( ( m1_pre_topc @ B @ A ) =>
% 4.57/4.76           ( ![C:$i]:
% 4.57/4.76             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.57/4.76               ( ![D:$i]:
% 4.57/4.76                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 4.57/4.76                   ( ( ( C ) = ( D ) ) =>
% 4.57/4.76                     ( ( v2_compts_1 @ C @ A ) <=> ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 4.57/4.76  thf('44', plain,
% 4.57/4.76      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 4.57/4.76         (~ (m1_pre_topc @ X18 @ X19)
% 4.57/4.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 4.57/4.76          | ~ (v2_compts_1 @ X21 @ X19)
% 4.57/4.76          | (v2_compts_1 @ X20 @ X18)
% 4.57/4.76          | ((X21) != (X20))
% 4.57/4.76          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 4.57/4.76          | ~ (l1_pre_topc @ X19))),
% 4.57/4.76      inference('cnf', [status(esa)], [t28_compts_1])).
% 4.57/4.76  thf('45', plain,
% 4.57/4.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X19)
% 4.57/4.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 4.57/4.76          | (v2_compts_1 @ X20 @ X18)
% 4.57/4.76          | ~ (v2_compts_1 @ X20 @ X19)
% 4.57/4.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 4.57/4.76          | ~ (m1_pre_topc @ X18 @ X19))),
% 4.57/4.76      inference('simplify', [status(thm)], ['44'])).
% 4.57/4.76  thf('46', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.76         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (m1_pre_topc @ X2 @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 4.57/4.76          | ~ (v2_compts_1 @ X1 @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | (v2_compts_1 @ X1 @ X2)
% 4.57/4.76          | ~ (l1_pre_topc @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['43', '45'])).
% 4.57/4.76  thf('47', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (l1_pre_topc @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | (v2_compts_1 @ X1 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (v2_compts_1 @ X1 @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ 
% 4.57/4.76               (k1_zfmisc_1 @ 
% 4.57/4.76                (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))))
% 4.57/4.76          | ~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['42', '46'])).
% 4.57/4.76  thf('48', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i]:
% 4.57/4.76         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ 
% 4.57/4.76               (k1_zfmisc_1 @ 
% 4.57/4.76                (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))))
% 4.57/4.76          | ~ (v2_compts_1 @ X1 @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | (v2_compts_1 @ X1 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('simplify', [status(thm)], ['47'])).
% 4.57/4.76  thf('49', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i]:
% 4.57/4.76         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (l1_pre_topc @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | (v2_compts_1 @ X1 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (v2_compts_1 @ X1 @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['31', '48'])).
% 4.57/4.76  thf('50', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i]:
% 4.57/4.76         (~ (v2_compts_1 @ X1 @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | (v2_compts_1 @ X1 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 4.57/4.76      inference('simplify', [status(thm)], ['49'])).
% 4.57/4.76  thf('51', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0)
% 4.57/4.76          | (v2_compts_1 @ X1 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (v2_compts_1 @ X1 @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['26', '50'])).
% 4.57/4.76  thf('52', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i]:
% 4.57/4.76         (~ (v2_compts_1 @ X1 @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | (v2_compts_1 @ X1 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('simplify', [status(thm)], ['51'])).
% 4.57/4.76  thf('53', plain,
% 4.57/4.76      (((~ (l1_pre_topc @ sk_A)
% 4.57/4.76         | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.57/4.76         | (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))))
% 4.57/4.76         <= (((v2_compts_1 @ sk_B @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['25', '52'])).
% 4.57/4.76  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('55', plain,
% 4.57/4.76      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.57/4.76         | (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))))
% 4.57/4.76         <= (((v2_compts_1 @ sk_B @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 4.57/4.76      inference('demod', [status(thm)], ['53', '54'])).
% 4.57/4.76  thf('56', plain,
% 4.57/4.76      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A))))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 4.57/4.76             ((v2_compts_1 @ sk_B @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['23', '55'])).
% 4.57/4.76  thf('57', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('sup-', [status(thm)], ['32', '33'])).
% 4.57/4.76  thf('58', plain,
% 4.57/4.76      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('split', [status(esa)], ['0'])).
% 4.57/4.76  thf('59', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76              = (u1_struct_0 @ X0)))),
% 4.57/4.76      inference('sup-', [status(thm)], ['29', '30'])).
% 4.57/4.76  thf('60', plain,
% 4.57/4.76      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('split', [status(esa)], ['0'])).
% 4.57/4.76  thf('61', plain,
% 4.57/4.76      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 4.57/4.76         (~ (m1_pre_topc @ X18 @ X19)
% 4.57/4.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 4.57/4.76          | ~ (v2_compts_1 @ X20 @ X18)
% 4.57/4.76          | (v2_compts_1 @ X21 @ X19)
% 4.57/4.76          | ((X21) != (X20))
% 4.57/4.76          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 4.57/4.76          | ~ (l1_pre_topc @ X19))),
% 4.57/4.76      inference('cnf', [status(esa)], [t28_compts_1])).
% 4.57/4.76  thf('62', plain,
% 4.57/4.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X19)
% 4.57/4.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 4.57/4.76          | (v2_compts_1 @ X20 @ X19)
% 4.57/4.76          | ~ (v2_compts_1 @ X20 @ X18)
% 4.57/4.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 4.57/4.76          | ~ (m1_pre_topc @ X18 @ X19))),
% 4.57/4.76      inference('simplify', [status(thm)], ['61'])).
% 4.57/4.76  thf('63', plain,
% 4.57/4.76      ((![X0 : $i]:
% 4.57/4.76          (~ (m1_pre_topc @ X0 @ sk_A)
% 4.57/4.76           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76           | ~ (v2_compts_1 @ sk_B @ X0)
% 4.57/4.76           | (v2_compts_1 @ sk_B @ sk_A)
% 4.57/4.76           | ~ (l1_pre_topc @ sk_A)))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['60', '62'])).
% 4.57/4.76  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('65', plain,
% 4.57/4.76      ((![X0 : $i]:
% 4.57/4.76          (~ (m1_pre_topc @ X0 @ sk_A)
% 4.57/4.76           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76           | ~ (v2_compts_1 @ sk_B @ X0)
% 4.57/4.76           | (v2_compts_1 @ sk_B @ sk_A)))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('demod', [status(thm)], ['63', '64'])).
% 4.57/4.76  thf('66', plain,
% 4.57/4.76      ((![X0 : $i]:
% 4.57/4.76          (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76           | ~ (l1_pre_topc @ X0)
% 4.57/4.76           | (v2_compts_1 @ sk_B @ sk_A)
% 4.57/4.76           | ~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76           | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ sk_A)))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['59', '65'])).
% 4.57/4.76  thf('67', plain,
% 4.57/4.76      (((~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) @ sk_A)
% 4.57/4.76         | ~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))
% 4.57/4.76         | (v2_compts_1 @ sk_B @ sk_A)
% 4.57/4.76         | ~ (l1_pre_topc @ sk_A)))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['58', '66'])).
% 4.57/4.76  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('69', plain,
% 4.57/4.76      (((~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) @ sk_A)
% 4.57/4.76         | ~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))
% 4.57/4.76         | (v2_compts_1 @ sk_B @ sk_A)))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('demod', [status(thm)], ['67', '68'])).
% 4.57/4.76  thf('70', plain,
% 4.57/4.76      (((~ (l1_pre_topc @ sk_A)
% 4.57/4.76         | (v2_compts_1 @ sk_B @ sk_A)
% 4.57/4.76         | ~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['57', '69'])).
% 4.57/4.76  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('72', plain,
% 4.57/4.76      ((((v2_compts_1 @ sk_B @ sk_A)
% 4.57/4.76         | ~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('demod', [status(thm)], ['70', '71'])).
% 4.57/4.76  thf('73', plain,
% 4.57/4.76      (((v2_compts_1 @ sk_B @ sk_A))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 4.57/4.76             ((v2_compts_1 @ sk_B @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['56', '72'])).
% 4.57/4.76  thf('74', plain,
% 4.57/4.76      ((~ (v2_compts_1 @ sk_B @ sk_A)) <= (~ ((v2_compts_1 @ sk_B @ sk_A)))),
% 4.57/4.76      inference('split', [status(esa)], ['16'])).
% 4.57/4.76  thf('75', plain,
% 4.57/4.76      (((v2_compts_1 @ sk_B @ sk_A)) | 
% 4.57/4.76       ~
% 4.57/4.76       ((v2_compts_1 @ sk_B @ 
% 4.57/4.76         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 4.57/4.76       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['73', '74'])).
% 4.57/4.76  thf('76', plain,
% 4.57/4.76      (((m1_subset_1 @ sk_B @ 
% 4.57/4.76         (k1_zfmisc_1 @ 
% 4.57/4.76          (u1_struct_0 @ 
% 4.57/4.76           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 4.57/4.76        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('77', plain,
% 4.57/4.76      (((m1_subset_1 @ sk_B @ 
% 4.57/4.76         (k1_zfmisc_1 @ 
% 4.57/4.76          (u1_struct_0 @ 
% 4.57/4.76           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))) | 
% 4.57/4.76       ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.57/4.76      inference('split', [status(esa)], ['76'])).
% 4.57/4.76  thf('78', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (((u1_struct_0 @ 
% 4.57/4.76            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76            = (u1_struct_0 @ X0))
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('clc', [status(thm)], ['11', '14'])).
% 4.57/4.76  thf('79', plain,
% 4.57/4.76      (((m1_subset_1 @ sk_B @ 
% 4.57/4.76         (k1_zfmisc_1 @ 
% 4.57/4.76          (u1_struct_0 @ 
% 4.57/4.76           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 4.57/4.76        | (v2_compts_1 @ sk_B @ sk_A))),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('80', plain,
% 4.57/4.76      (((m1_subset_1 @ sk_B @ 
% 4.57/4.76         (k1_zfmisc_1 @ 
% 4.57/4.76          (u1_struct_0 @ 
% 4.57/4.76           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ 
% 4.57/4.76               (k1_zfmisc_1 @ 
% 4.57/4.76                (u1_struct_0 @ 
% 4.57/4.76                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 4.57/4.76      inference('split', [status(esa)], ['79'])).
% 4.57/4.76  thf('81', plain,
% 4.57/4.76      ((((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.57/4.76         | ~ (l1_pre_topc @ sk_A)))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ 
% 4.57/4.76               (k1_zfmisc_1 @ 
% 4.57/4.76                (u1_struct_0 @ 
% 4.57/4.76                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 4.57/4.76      inference('sup+', [status(thm)], ['78', '80'])).
% 4.57/4.76  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('83', plain,
% 4.57/4.76      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ 
% 4.57/4.76               (k1_zfmisc_1 @ 
% 4.57/4.76                (u1_struct_0 @ 
% 4.57/4.76                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 4.57/4.76      inference('demod', [status(thm)], ['81', '82'])).
% 4.57/4.76  thf('84', plain,
% 4.57/4.76      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.57/4.76         <= (~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('split', [status(esa)], ['16'])).
% 4.57/4.76  thf('85', plain,
% 4.57/4.76      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 4.57/4.76       ~
% 4.57/4.76       ((m1_subset_1 @ sk_B @ 
% 4.57/4.76         (k1_zfmisc_1 @ 
% 4.57/4.76          (u1_struct_0 @ 
% 4.57/4.76           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['83', '84'])).
% 4.57/4.76  thf('86', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('sup-', [status(thm)], ['32', '33'])).
% 4.57/4.76  thf('87', plain,
% 4.57/4.76      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('split', [status(esa)], ['0'])).
% 4.57/4.76  thf('88', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76              = (u1_struct_0 @ X0)))),
% 4.57/4.76      inference('sup-', [status(thm)], ['29', '30'])).
% 4.57/4.76  thf('89', plain,
% 4.57/4.76      (((v2_compts_1 @ sk_B @ sk_A)) <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 4.57/4.76      inference('split', [status(esa)], ['24'])).
% 4.57/4.76  thf('90', plain,
% 4.57/4.76      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('split', [status(esa)], ['0'])).
% 4.57/4.76  thf('91', plain,
% 4.57/4.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X19)
% 4.57/4.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 4.57/4.76          | (v2_compts_1 @ X20 @ X18)
% 4.57/4.76          | ~ (v2_compts_1 @ X20 @ X19)
% 4.57/4.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 4.57/4.76          | ~ (m1_pre_topc @ X18 @ X19))),
% 4.57/4.76      inference('simplify', [status(thm)], ['44'])).
% 4.57/4.76  thf('92', plain,
% 4.57/4.76      ((![X0 : $i]:
% 4.57/4.76          (~ (m1_pre_topc @ X0 @ sk_A)
% 4.57/4.76           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76           | ~ (v2_compts_1 @ sk_B @ sk_A)
% 4.57/4.76           | (v2_compts_1 @ sk_B @ X0)
% 4.57/4.76           | ~ (l1_pre_topc @ sk_A)))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['90', '91'])).
% 4.57/4.76  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('94', plain,
% 4.57/4.76      ((![X0 : $i]:
% 4.57/4.76          (~ (m1_pre_topc @ X0 @ sk_A)
% 4.57/4.76           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76           | ~ (v2_compts_1 @ sk_B @ sk_A)
% 4.57/4.76           | (v2_compts_1 @ sk_B @ X0)))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('demod', [status(thm)], ['92', '93'])).
% 4.57/4.76  thf('95', plain,
% 4.57/4.76      ((![X0 : $i]:
% 4.57/4.76          ((v2_compts_1 @ sk_B @ X0)
% 4.57/4.76           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76           | ~ (m1_pre_topc @ X0 @ sk_A)))
% 4.57/4.76         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 4.57/4.76             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['89', '94'])).
% 4.57/4.76  thf('96', plain,
% 4.57/4.76      ((![X0 : $i]:
% 4.57/4.76          (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76           | ~ (l1_pre_topc @ X0)
% 4.57/4.76           | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ sk_A)
% 4.57/4.76           | (v2_compts_1 @ sk_B @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))))
% 4.57/4.76         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 4.57/4.76             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['88', '95'])).
% 4.57/4.76  thf('97', plain,
% 4.57/4.76      ((((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))
% 4.57/4.76         | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) @ sk_A)
% 4.57/4.76         | ~ (l1_pre_topc @ sk_A)))
% 4.57/4.76         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 4.57/4.76             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['87', '96'])).
% 4.57/4.76  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('99', plain,
% 4.57/4.76      ((((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))
% 4.57/4.76         | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) @ sk_A)))
% 4.57/4.76         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 4.57/4.76             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('demod', [status(thm)], ['97', '98'])).
% 4.57/4.76  thf('100', plain,
% 4.57/4.76      (((~ (l1_pre_topc @ sk_A)
% 4.57/4.76         | (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))))
% 4.57/4.76         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 4.57/4.76             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['86', '99'])).
% 4.57/4.76  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('102', plain,
% 4.57/4.76      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A))))
% 4.57/4.76         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 4.57/4.76             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('demod', [status(thm)], ['100', '101'])).
% 4.57/4.76  thf('103', plain,
% 4.57/4.76      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('split', [status(esa)], ['0'])).
% 4.57/4.76  thf('104', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | (l1_pre_topc @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['12', '13'])).
% 4.57/4.76  thf('105', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76              = (u1_struct_0 @ X0)))),
% 4.57/4.76      inference('sup-', [status(thm)], ['29', '30'])).
% 4.57/4.76  thf('106', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.57/4.76      inference('clc', [status(thm)], ['37', '41'])).
% 4.57/4.76  thf('107', plain,
% 4.57/4.76      (![X0 : $i]:
% 4.57/4.76         (((u1_struct_0 @ 
% 4.57/4.76            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76            = (u1_struct_0 @ X0))
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('clc', [status(thm)], ['11', '14'])).
% 4.57/4.76  thf('108', plain,
% 4.57/4.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X19)
% 4.57/4.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 4.57/4.76          | (v2_compts_1 @ X20 @ X19)
% 4.57/4.76          | ~ (v2_compts_1 @ X20 @ X18)
% 4.57/4.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 4.57/4.76          | ~ (m1_pre_topc @ X18 @ X19))),
% 4.57/4.76      inference('simplify', [status(thm)], ['61'])).
% 4.57/4.76  thf('109', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.76         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (m1_pre_topc @ X2 @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 4.57/4.76          | ~ (v2_compts_1 @ X1 @ X2)
% 4.57/4.76          | (v2_compts_1 @ X1 @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['107', '108'])).
% 4.57/4.76  thf('110', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (l1_pre_topc @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | (v2_compts_1 @ X1 @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (v2_compts_1 @ X1 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ 
% 4.57/4.76               (k1_zfmisc_1 @ 
% 4.57/4.76                (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))))
% 4.57/4.76          | ~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['106', '109'])).
% 4.57/4.76  thf('111', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i]:
% 4.57/4.76         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ 
% 4.57/4.76               (k1_zfmisc_1 @ 
% 4.57/4.76                (u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))))
% 4.57/4.76          | ~ (v2_compts_1 @ X1 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | (v2_compts_1 @ X1 @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('simplify', [status(thm)], ['110'])).
% 4.57/4.76  thf('112', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i]:
% 4.57/4.76         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (l1_pre_topc @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | (v2_compts_1 @ X1 @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (v2_compts_1 @ X1 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['105', '111'])).
% 4.57/4.76  thf('113', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i]:
% 4.57/4.76         (~ (v2_compts_1 @ X1 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | (v2_compts_1 @ X1 @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 4.57/4.76      inference('simplify', [status(thm)], ['112'])).
% 4.57/4.76  thf('114', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i]:
% 4.57/4.76         (~ (l1_pre_topc @ X0)
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0)
% 4.57/4.76          | (v2_compts_1 @ X1 @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (v2_compts_1 @ X1 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['104', '113'])).
% 4.57/4.76  thf('115', plain,
% 4.57/4.76      (![X0 : $i, X1 : $i]:
% 4.57/4.76         (~ (v2_compts_1 @ X1 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | (v2_compts_1 @ X1 @ 
% 4.57/4.76             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 4.57/4.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.57/4.76          | ~ (l1_pre_topc @ X0))),
% 4.57/4.76      inference('simplify', [status(thm)], ['114'])).
% 4.57/4.76  thf('116', plain,
% 4.57/4.76      (((~ (l1_pre_topc @ sk_A)
% 4.57/4.76         | (v2_compts_1 @ sk_B @ 
% 4.57/4.76            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.57/4.76         | ~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['103', '115'])).
% 4.57/4.76  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 4.57/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.76  thf('118', plain,
% 4.57/4.76      ((((v2_compts_1 @ sk_B @ 
% 4.57/4.76          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 4.57/4.76         | ~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)))))
% 4.57/4.76         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('demod', [status(thm)], ['116', '117'])).
% 4.57/4.76  thf('119', plain,
% 4.57/4.76      (((v2_compts_1 @ sk_B @ 
% 4.57/4.76         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 4.57/4.76         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 4.57/4.76             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['102', '118'])).
% 4.57/4.76  thf('120', plain,
% 4.57/4.76      ((~ (v2_compts_1 @ sk_B @ 
% 4.57/4.76           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 4.57/4.76         <= (~
% 4.57/4.76             ((v2_compts_1 @ sk_B @ 
% 4.57/4.76               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 4.57/4.76      inference('split', [status(esa)], ['16'])).
% 4.57/4.76  thf('121', plain,
% 4.57/4.76      (~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 4.57/4.76       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 4.57/4.76       ((v2_compts_1 @ sk_B @ 
% 4.57/4.76         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 4.57/4.76      inference('sup-', [status(thm)], ['119', '120'])).
% 4.57/4.76  thf('122', plain,
% 4.57/4.76      (((v2_compts_1 @ sk_B @ sk_A)) | 
% 4.57/4.76       ((v2_compts_1 @ sk_B @ 
% 4.57/4.76         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 4.57/4.76      inference('split', [status(esa)], ['24'])).
% 4.57/4.76  thf('123', plain, ($false),
% 4.57/4.76      inference('sat_resolution*', [status(thm)],
% 4.57/4.76                ['21', '22', '75', '77', '85', '121', '122'])).
% 4.57/4.76  
% 4.57/4.76  % SZS output end Refutation
% 4.57/4.76  
% 4.57/4.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
