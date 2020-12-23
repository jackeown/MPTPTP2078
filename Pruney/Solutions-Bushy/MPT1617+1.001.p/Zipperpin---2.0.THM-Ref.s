%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1617+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L8WayGJWG3

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:51 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 203 expanded)
%              Number of leaves         :   38 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  936 (2125 expanded)
%              Number of equality atoms :   22 (  44 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t25_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_tops_2 @ B @ A )
            <=> ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_yellow_1])).

thf('0',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( m1_subset_1 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ X2 )
      | ~ ( r2_hidden @ X3 @ X1 )
      | ( v3_pre_topc @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( v3_pre_topc @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A )
        | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ sk_B ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ( r2_hidden @ X9 @ ( u1_pre_topc @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_C_1 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
      | ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf(dt_k1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k1_yellow_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k1_yellow_1 @ A ) @ A )
      & ( v8_relat_2 @ ( k1_yellow_1 @ A ) )
      & ( v4_relat_2 @ ( k1_yellow_1 @ A ) )
      & ( v1_relat_2 @ ( k1_yellow_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k1_yellow_1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_1])).

thf(redefinition_k1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k1_yellow_1 @ A )
      = ( k1_wellord2 @ A ) ) )).

thf('32',plain,(
    ! [X22: $i] :
      ( ( k1_yellow_1 @ X22 )
      = ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_yellow_1])).

thf('33',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k1_wellord2 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( ( g1_orders_2 @ X20 @ X21 )
       != ( g1_orders_2 @ X18 @ X19 ) )
      | ( X20 = X18 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( g1_orders_2 @ X0 @ ( k1_wellord2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k2_yellow_1 @ A )
      = ( g1_orders_2 @ A @ ( k1_yellow_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X4: $i] :
      ( ( k2_yellow_1 @ X4 )
      = ( g1_orders_2 @ X4 @ ( k1_yellow_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('37',plain,(
    ! [X22: $i] :
      ( ( k1_yellow_1 @ X22 )
      = ( k1_wellord2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_yellow_1])).

thf('38',plain,(
    ! [X4: $i] :
      ( ( k2_yellow_1 @ X4 )
      = ( g1_orders_2 @ X4 @ ( k1_wellord2 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( k2_yellow_1 @ X0 )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_yellow_1 @ X1 )
       != X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( X1
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) )
      | ~ ( v1_orders_2 @ ( k2_yellow_1 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X17: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('43',plain,(
    ! [X16: $i] :
      ( v1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('44',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('49',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['41','42','43'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ X1 )
      | ( v1_tops_2 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf('56',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( v1_tops_2 @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      | ( v1_tops_2 @ sk_B @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['49','60'])).

thf('62',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('64',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X9 @ ( u1_pre_topc @ X10 ) )
      | ( v3_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('66',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X1 @ X2 ) @ X2 )
      | ( v1_tops_2 @ X1 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['68','73'])).

thf('75',plain,
    ( ( v1_tops_2 @ sk_B @ sk_A )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['61','74'])).

thf('76',plain,
    ( ~ ( v1_tops_2 @ sk_B @ sk_A )
   <= ~ ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( v1_tops_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','47','48','77'])).


%------------------------------------------------------------------------------
