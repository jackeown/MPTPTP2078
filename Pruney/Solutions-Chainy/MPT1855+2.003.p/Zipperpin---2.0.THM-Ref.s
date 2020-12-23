%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gd8RxRpFpW

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:10 EST 2020

% Result     : Theorem 9.42s
% Output     : Refutation 9.42s
% Verified   : 
% Statistics : Number of formulae       :  417 (45365 expanded)
%              Number of leaves         :   33 (12862 expanded)
%              Depth                    :   53
%              Number of atoms          : 4231 (612444 expanded)
%              Number of equality atoms :  126 (12207 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t23_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v7_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ? [C: $i] :
              ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ ( k1_tex_2 @ A @ C ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ A @ C ) ) ) )
              & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v7_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ? [C: $i] :
                ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ ( k1_tex_2 @ A @ C ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ A @ C ) ) ) )
                & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( m1_pre_topc @ X13 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( r1_tarski @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ X18 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( r1_tarski @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ( m1_pre_topc @ X13 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) @ sk_B_1 )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) @ sk_B_1 ),
    inference(demod,[status(thm)],['40','45','50'])).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( r1_tarski @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('55',plain,(
    r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['23','55'])).

thf('57',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('58',plain,(
    r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( ( u1_struct_0 @ sk_B_1 )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(d1_tex_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( ( v7_struct_0 @ A )
      <=> ? [B: $i] :
            ( ( ( u1_struct_0 @ A )
              = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
            & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X21: $i] :
      ( ~ ( v7_struct_0 @ X21 )
      | ( ( u1_struct_0 @ X21 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ ( sk_B @ X21 ) ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('67',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ( m1_pre_topc @ X13 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['65','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('74',plain,(
    m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ( m1_pre_topc @ X13 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('80',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('81',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('82',plain,(
    m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X13 @ ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( u1_pre_topc @ X12 ) ) )
      | ( m1_pre_topc @ X13 @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('86',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('87',plain,(
    m1_pre_topc @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X21: $i] :
      ( ~ ( v7_struct_0 @ X21 )
      | ( m1_subset_1 @ ( sk_B @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('89',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( v7_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['87','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('94',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('95',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['92','95','96','97'])).

thf('99',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['99','100'])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('102',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X26 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('103',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('105',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( r1_tarski @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('109',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('111',plain,(
    r1_tarski @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('113',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ),
    inference(clc,[status(thm)],['105','106'])).

thf('115',plain,(
    ! [X21: $i] :
      ( ~ ( v7_struct_0 @ X21 )
      | ( m1_subset_1 @ ( sk_B @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('116',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( v1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf(d4_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_tex_2 @ A @ B ) )
              <=> ( ( u1_struct_0 @ C )
                  = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('119',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( X25
       != ( k1_tex_2 @ X24 @ X23 ) )
      | ( ( u1_struct_0 @ X25 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X24 ) @ X23 ) )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ~ ( v1_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('120',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X24 @ X23 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X24 @ X23 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X24 @ X23 ) @ X24 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X24 @ X23 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X24 ) @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) @ X0 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( v7_struct_0 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['114','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('125',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('127',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('132',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('133',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('135',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['130','137'])).

thf('139',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['130','137'])).

thf('140',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['113','138','139'])).

thf('141',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( v7_struct_0 @ sk_B_1 )
    | ( ( u1_struct_0 @ sk_B_1 )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['64','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('143',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('145',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( u1_struct_0 @ sk_B_1 )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['141','143','144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( ( u1_struct_0 @ X25 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X24 ) @ X23 ) )
      | ( X25
        = ( k1_tex_2 @ X24 @ X23 ) )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ~ ( v1_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( X0
        = ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('152',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( X0
        = ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
     != ( u1_struct_0 @ sk_B_1 ) )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
      = ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_B_1 )
    | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','153'])).

thf('155',plain,(
    m1_pre_topc @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('156',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('157',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('159',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_B_1 ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('162',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
     != ( u1_struct_0 @ sk_B_1 ) )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
      = ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['154','159','164'])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
      = ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
      = ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('173',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('175',plain,(
    ! [X7: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ~ ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('180',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['178','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['177','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['176','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['175','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('189',plain,(
    ! [X7: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ~ ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['187','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['171','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['170','195'])).

thf('197',plain,
    ( ~ ( l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['169','196'])).

thf('198',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('199',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('200',plain,(
    l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('202',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('204',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('206',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('207',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,
    ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['197','200','201','207'])).

thf('209',plain,(
    ! [X21: $i] :
      ( ~ ( v7_struct_0 @ X21 )
      | ( ( u1_struct_0 @ X21 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ ( sk_B @ X21 ) ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('210',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['130','137'])).

thf('211',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('212',plain,
    ( ~ ( v1_xboole_0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ),
    inference(clc,[status(thm)],['105','106'])).

thf('214',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('215',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('217',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('219',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ~ ( v1_xboole_0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['212','219'])).

thf('221',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('222',plain,(
    ~ ( v1_xboole_0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['220','221'])).

thf('223',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( v7_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['209','222'])).

thf('224',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('225',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['223','224','225'])).

thf('227',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,(
    ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['208','228'])).

thf('230',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
    = ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['168','229'])).

thf('231',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('232',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('234',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( v7_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('236',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['234','235','236','237'])).

thf('239',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['238','239'])).

thf('241',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['240','241'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('243',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('244',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( ( u1_struct_0 @ X25 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X24 ) @ X23 ) )
      | ( X25
        = ( k1_tex_2 @ X24 @ X23 ) )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ~ ( v1_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( X0
        = ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['240','241'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( X0
        = ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['246','247','248'])).

thf('250',plain,(
    ! [X21: $i] :
      ( ~ ( v7_struct_0 @ X21 )
      | ( ( u1_struct_0 @ X21 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ ( sk_B @ X21 ) ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('251',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('252',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('253',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( v7_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['250','253'])).

thf('255',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('256',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['254','255','256'])).

thf('258',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['257','258'])).

thf('260',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('261',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('263',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['261','262'])).

thf('264',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( X0
        = ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['249','265'])).

thf('267',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
     != ( u1_struct_0 @ sk_B_1 ) )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
      = ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A )
    | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['231','266'])).

thf('268',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf('269',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('270',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
     != ( u1_struct_0 @ sk_B_1 ) )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
      = ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['267','268','269'])).

thf('271',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
      = ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['270'])).

thf('272',plain,(
    ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['208','228'])).

thf('273',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
      = ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['271','272'])).

thf('274',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
      = ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['273','274'])).

thf('276',plain,
    ( ( ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
      = ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['230','275'])).

thf('277',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('278',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['263','264'])).

thf('279',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['277','278'])).

thf('280',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['240','241'])).

thf('281',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('282',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['282','283'])).

thf('285',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['284','285'])).

thf('287',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X24 @ X23 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X24 @ X23 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X24 @ X23 ) @ X24 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X24 @ X23 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X24 ) @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('288',plain,
    ( ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['240','241'])).

thf('290',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['288','289','290'])).

thf('292',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['240','241'])).

thf('293',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X26 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('294',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['294','295'])).

thf('297',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['296','297'])).

thf('299',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['291','298'])).

thf('300',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['240','241'])).

thf('301',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('302',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['300','301'])).

thf('303',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['302','303'])).

thf('305',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['304','305'])).

thf('307',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['299','306'])).

thf('308',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['307','308'])).

thf('310',plain,(
    ! [X28: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ X28 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
     != ( g1_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['240','241'])).

thf('313',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
 != ( g1_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['311','312'])).

thf('314',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['279','313'])).

thf('315',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
    = ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['168','229'])).

thf('316',plain,
    ( ( ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['314','315'])).

thf('317',plain,
    ( ( ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['276','316'])).

thf('318',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['317'])).

thf('319',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['130','137'])).

thf('320',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('321',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['319','320'])).

thf('322',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('323',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ) )
    | ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['321','322'])).

thf('324',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['319','320'])).

thf('325',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('326',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('327',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( X0
        = ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('328',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
     != ( u1_struct_0 @ sk_B_1 ) )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
      = ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) @ sk_B_1 )
    | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['326','327'])).

thf('329',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['319','320'])).

thf('330',plain,(
    ! [X21: $i] :
      ( ~ ( v7_struct_0 @ X21 )
      | ( m1_subset_1 @ ( sk_B @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('331',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X26 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('332',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( m1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['330','331'])).

thf('333',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['332'])).

thf('334',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('335',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['333','334'])).

thf('336',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['335'])).

thf('337',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( v7_struct_0 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['329','336'])).

thf('338',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('339',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('341',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['337','338','339','340'])).

thf('342',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) @ sk_B_1 ),
    inference(clc,[status(thm)],['341','342'])).

thf('344',plain,(
    ! [X21: $i] :
      ( ~ ( v7_struct_0 @ X21 )
      | ( ( u1_struct_0 @ X21 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ ( sk_B @ X21 ) ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('345',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ),
    inference(clc,[status(thm)],['105','106'])).

thf('346',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('347',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['345','346'])).

thf('348',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('349',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['347','348'])).

thf('350',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['130','137'])).

thf('351',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['349','350'])).

thf('352',plain,
    ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( v7_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['344','351'])).

thf('353',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('354',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,
    ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['352','353','354'])).

thf('356',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('357',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['355','356'])).

thf('358',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
     != ( u1_struct_0 @ sk_B_1 ) )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
      = ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['328','343','357'])).

thf('359',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
      = ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['358'])).

thf('360',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
      = ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['359','360'])).

thf('362',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('363',plain,(
    ! [X7: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ~ ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('364',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['362','363'])).

thf('365',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['319','320'])).

thf('366',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('367',plain,
    ( ( l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['365','366'])).

thf('368',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('369',plain,(
    l1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['367','368'])).

thf('370',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['364','369'])).

thf('371',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('372',plain,(
    ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['370','371'])).

thf('373',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
    = ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['361','372'])).

thf('374',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
     != ( k1_tex_2 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['318','373'])).

thf('375',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['374'])).

thf('376',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('377',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['375','376'])).

thf('378',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('379',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('380',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['378','379'])).

thf('381',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['377','380'])).

thf('382',plain,(
    $false ),
    inference(demod,[status(thm)],['0','381'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gd8RxRpFpW
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:21:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 9.42/9.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.42/9.61  % Solved by: fo/fo7.sh
% 9.42/9.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.42/9.61  % done 2919 iterations in 9.141s
% 9.42/9.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.42/9.61  % SZS output start Refutation
% 9.42/9.61  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 9.42/9.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 9.42/9.61  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 9.42/9.61  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 9.42/9.61  thf(sk_A_type, type, sk_A: $i).
% 9.42/9.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 9.42/9.61  thf(sk_B_type, type, sk_B: $i > $i).
% 9.42/9.61  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 9.42/9.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 9.42/9.61  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 9.42/9.61  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 9.42/9.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.42/9.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.42/9.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 9.42/9.61  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 9.42/9.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.42/9.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 9.42/9.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 9.42/9.61  thf(t23_tex_2, conjecture,
% 9.42/9.61    (![A:$i]:
% 9.42/9.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 9.42/9.61       ( ![B:$i]:
% 9.42/9.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v7_struct_0 @ B ) & 
% 9.42/9.61             ( m1_pre_topc @ B @ A ) ) =>
% 9.42/9.61           ( ?[C:$i]:
% 9.42/9.61             ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 9.42/9.61                 ( g1_pre_topc @
% 9.42/9.61                   ( u1_struct_0 @ ( k1_tex_2 @ A @ C ) ) @ 
% 9.42/9.61                   ( u1_pre_topc @ ( k1_tex_2 @ A @ C ) ) ) ) & 
% 9.42/9.61               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 9.42/9.61  thf(zf_stmt_0, negated_conjecture,
% 9.42/9.61    (~( ![A:$i]:
% 9.42/9.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 9.42/9.61          ( ![B:$i]:
% 9.42/9.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( v7_struct_0 @ B ) & 
% 9.42/9.61                ( m1_pre_topc @ B @ A ) ) =>
% 9.42/9.61              ( ?[C:$i]:
% 9.42/9.61                ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 9.42/9.61                    ( g1_pre_topc @
% 9.42/9.61                      ( u1_struct_0 @ ( k1_tex_2 @ A @ C ) ) @ 
% 9.42/9.61                      ( u1_pre_topc @ ( k1_tex_2 @ A @ C ) ) ) ) & 
% 9.42/9.61                  ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 9.42/9.61    inference('cnf.neg', [status(esa)], [t23_tex_2])).
% 9.42/9.61  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 9.42/9.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.61  thf(t2_tsep_1, axiom,
% 9.42/9.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 9.42/9.61  thf('1', plain,
% 9.42/9.61      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 9.42/9.61      inference('cnf', [status(esa)], [t2_tsep_1])).
% 9.42/9.61  thf(t65_pre_topc, axiom,
% 9.42/9.61    (![A:$i]:
% 9.42/9.61     ( ( l1_pre_topc @ A ) =>
% 9.42/9.61       ( ![B:$i]:
% 9.42/9.61         ( ( l1_pre_topc @ B ) =>
% 9.42/9.61           ( ( m1_pre_topc @ A @ B ) <=>
% 9.42/9.61             ( m1_pre_topc @
% 9.42/9.61               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 9.42/9.61  thf('2', plain,
% 9.42/9.61      (![X12 : $i, X13 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X12)
% 9.42/9.61          | ~ (m1_pre_topc @ X13 @ X12)
% 9.42/9.61          | (m1_pre_topc @ X13 @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 9.42/9.61          | ~ (l1_pre_topc @ X13))),
% 9.42/9.61      inference('cnf', [status(esa)], [t65_pre_topc])).
% 9.42/9.61  thf('3', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X0)
% 9.42/9.61          | ~ (l1_pre_topc @ X0)
% 9.42/9.61          | (m1_pre_topc @ X0 @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('sup-', [status(thm)], ['1', '2'])).
% 9.42/9.61  thf('4', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         ((m1_pre_topc @ X0 @ 
% 9.42/9.61           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('simplify', [status(thm)], ['3'])).
% 9.42/9.61  thf(t35_borsuk_1, axiom,
% 9.42/9.61    (![A:$i]:
% 9.42/9.61     ( ( l1_pre_topc @ A ) =>
% 9.42/9.61       ( ![B:$i]:
% 9.42/9.61         ( ( m1_pre_topc @ B @ A ) =>
% 9.42/9.61           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 9.42/9.61  thf('5', plain,
% 9.42/9.61      (![X19 : $i, X20 : $i]:
% 9.42/9.61         (~ (m1_pre_topc @ X19 @ X20)
% 9.42/9.61          | (r1_tarski @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 9.42/9.61          | ~ (l1_pre_topc @ X20))),
% 9.42/9.61      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 9.42/9.61  thf('6', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X0)
% 9.42/9.61          | ~ (l1_pre_topc @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.61          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 9.42/9.61             (u1_struct_0 @ 
% 9.42/9.61              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))),
% 9.42/9.61      inference('sup-', [status(thm)], ['4', '5'])).
% 9.42/9.61  thf('7', plain,
% 9.42/9.61      (![X18 : $i]: ((m1_pre_topc @ X18 @ X18) | ~ (l1_pre_topc @ X18))),
% 9.42/9.61      inference('cnf', [status(esa)], [t2_tsep_1])).
% 9.42/9.61  thf(t11_tmap_1, axiom,
% 9.42/9.61    (![A:$i]:
% 9.42/9.61     ( ( l1_pre_topc @ A ) =>
% 9.42/9.61       ( ![B:$i]:
% 9.42/9.61         ( ( m1_pre_topc @ B @ A ) =>
% 9.42/9.61           ( ( v1_pre_topc @
% 9.42/9.61               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 9.42/9.61             ( m1_pre_topc @
% 9.42/9.61               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 9.42/9.61  thf('8', plain,
% 9.42/9.61      (![X16 : $i, X17 : $i]:
% 9.42/9.61         (~ (m1_pre_topc @ X16 @ X17)
% 9.42/9.61          | (m1_pre_topc @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)) @ X17)
% 9.42/9.61          | ~ (l1_pre_topc @ X17))),
% 9.42/9.61      inference('cnf', [status(esa)], [t11_tmap_1])).
% 9.42/9.61  thf('9', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X0)
% 9.42/9.61          | ~ (l1_pre_topc @ X0)
% 9.42/9.61          | (m1_pre_topc @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 9.42/9.61      inference('sup-', [status(thm)], ['7', '8'])).
% 9.42/9.61  thf('10', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         ((m1_pre_topc @ 
% 9.42/9.61           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('simplify', [status(thm)], ['9'])).
% 9.42/9.61  thf(dt_m1_pre_topc, axiom,
% 9.42/9.61    (![A:$i]:
% 9.42/9.61     ( ( l1_pre_topc @ A ) =>
% 9.42/9.61       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 9.42/9.61  thf('11', plain,
% 9.42/9.61      (![X5 : $i, X6 : $i]:
% 9.42/9.61         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 9.42/9.61      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 9.42/9.61  thf('12', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X0)
% 9.42/9.61          | ~ (l1_pre_topc @ X0)
% 9.42/9.61          | (l1_pre_topc @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 9.42/9.61      inference('sup-', [status(thm)], ['10', '11'])).
% 9.42/9.61  thf('13', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         ((l1_pre_topc @ 
% 9.42/9.61           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('simplify', [status(thm)], ['12'])).
% 9.42/9.61  thf('14', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         ((r1_tarski @ (u1_struct_0 @ X0) @ 
% 9.42/9.61           (u1_struct_0 @ 
% 9.42/9.61            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('clc', [status(thm)], ['6', '13'])).
% 9.42/9.61  thf('15', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         ((r1_tarski @ (u1_struct_0 @ X0) @ 
% 9.42/9.61           (u1_struct_0 @ 
% 9.42/9.61            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('clc', [status(thm)], ['6', '13'])).
% 9.42/9.61  thf('16', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         ((m1_pre_topc @ 
% 9.42/9.61           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('simplify', [status(thm)], ['9'])).
% 9.42/9.61  thf('17', plain,
% 9.42/9.61      (![X19 : $i, X20 : $i]:
% 9.42/9.61         (~ (m1_pre_topc @ X19 @ X20)
% 9.42/9.61          | (r1_tarski @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 9.42/9.61          | ~ (l1_pre_topc @ X20))),
% 9.42/9.61      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 9.42/9.61  thf('18', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X0)
% 9.42/9.61          | ~ (l1_pre_topc @ X0)
% 9.42/9.61          | (r1_tarski @ 
% 9.42/9.61             (u1_struct_0 @ 
% 9.42/9.61              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 9.42/9.61             (u1_struct_0 @ X0)))),
% 9.42/9.61      inference('sup-', [status(thm)], ['16', '17'])).
% 9.42/9.61  thf('19', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         ((r1_tarski @ 
% 9.42/9.61           (u1_struct_0 @ 
% 9.42/9.61            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 9.42/9.61           (u1_struct_0 @ X0))
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('simplify', [status(thm)], ['18'])).
% 9.42/9.61  thf(d10_xboole_0, axiom,
% 9.42/9.61    (![A:$i,B:$i]:
% 9.42/9.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.42/9.61  thf('20', plain,
% 9.42/9.61      (![X0 : $i, X2 : $i]:
% 9.42/9.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.42/9.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.42/9.61  thf('21', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X0)
% 9.42/9.61          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 9.42/9.61               (u1_struct_0 @ 
% 9.42/9.61                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.61          | ((u1_struct_0 @ X0)
% 9.42/9.61              = (u1_struct_0 @ 
% 9.42/9.61                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))),
% 9.42/9.61      inference('sup-', [status(thm)], ['19', '20'])).
% 9.42/9.61  thf('22', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X0)
% 9.42/9.61          | ((u1_struct_0 @ X0)
% 9.42/9.61              = (u1_struct_0 @ 
% 9.42/9.61                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('sup-', [status(thm)], ['15', '21'])).
% 9.42/9.61  thf('23', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         (((u1_struct_0 @ X0)
% 9.42/9.61            = (u1_struct_0 @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('simplify', [status(thm)], ['22'])).
% 9.42/9.61  thf('24', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 9.42/9.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.61  thf('25', plain,
% 9.42/9.61      (![X16 : $i, X17 : $i]:
% 9.42/9.61         (~ (m1_pre_topc @ X16 @ X17)
% 9.42/9.61          | (m1_pre_topc @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)) @ X17)
% 9.42/9.61          | ~ (l1_pre_topc @ X17))),
% 9.42/9.61      inference('cnf', [status(esa)], [t11_tmap_1])).
% 9.42/9.61  thf('26', plain,
% 9.42/9.61      ((~ (l1_pre_topc @ sk_A)
% 9.42/9.61        | (m1_pre_topc @ 
% 9.42/9.61           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)) @ 
% 9.42/9.61           sk_A))),
% 9.42/9.61      inference('sup-', [status(thm)], ['24', '25'])).
% 9.42/9.61  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 9.42/9.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.61  thf('28', plain,
% 9.42/9.61      ((m1_pre_topc @ 
% 9.42/9.61        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)) @ sk_A)),
% 9.42/9.61      inference('demod', [status(thm)], ['26', '27'])).
% 9.42/9.61  thf('29', plain,
% 9.42/9.61      (![X16 : $i, X17 : $i]:
% 9.42/9.61         (~ (m1_pre_topc @ X16 @ X17)
% 9.42/9.61          | (m1_pre_topc @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)) @ X17)
% 9.42/9.61          | ~ (l1_pre_topc @ X17))),
% 9.42/9.61      inference('cnf', [status(esa)], [t11_tmap_1])).
% 9.42/9.61  thf('30', plain,
% 9.42/9.61      ((~ (l1_pre_topc @ sk_A)
% 9.42/9.61        | (m1_pre_topc @ 
% 9.42/9.61           (g1_pre_topc @ 
% 9.42/9.61            (u1_struct_0 @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))) @ 
% 9.42/9.61            (u1_pre_topc @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) @ 
% 9.42/9.61           sk_A))),
% 9.42/9.61      inference('sup-', [status(thm)], ['28', '29'])).
% 9.42/9.61  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 9.42/9.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.61  thf('32', plain,
% 9.42/9.61      ((m1_pre_topc @ 
% 9.42/9.61        (g1_pre_topc @ 
% 9.42/9.61         (u1_struct_0 @ 
% 9.42/9.61          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))) @ 
% 9.42/9.61         (u1_pre_topc @ 
% 9.42/9.61          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) @ 
% 9.42/9.61        sk_A)),
% 9.42/9.61      inference('demod', [status(thm)], ['30', '31'])).
% 9.42/9.61  thf('33', plain,
% 9.42/9.61      (![X5 : $i, X6 : $i]:
% 9.42/9.61         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 9.42/9.61      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 9.42/9.61  thf('34', plain,
% 9.42/9.61      ((~ (l1_pre_topc @ sk_A)
% 9.42/9.61        | (l1_pre_topc @ 
% 9.42/9.61           (g1_pre_topc @ 
% 9.42/9.61            (u1_struct_0 @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))) @ 
% 9.42/9.61            (u1_pre_topc @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 9.42/9.61      inference('sup-', [status(thm)], ['32', '33'])).
% 9.42/9.61  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 9.42/9.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.61  thf('36', plain,
% 9.42/9.61      ((l1_pre_topc @ 
% 9.42/9.61        (g1_pre_topc @ 
% 9.42/9.61         (u1_struct_0 @ 
% 9.42/9.61          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))) @ 
% 9.42/9.61         (u1_pre_topc @ 
% 9.42/9.61          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 9.42/9.61      inference('demod', [status(thm)], ['34', '35'])).
% 9.42/9.61  thf('37', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         ((m1_pre_topc @ 
% 9.42/9.61           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('simplify', [status(thm)], ['9'])).
% 9.42/9.61  thf('38', plain,
% 9.42/9.61      (![X12 : $i, X13 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X12)
% 9.42/9.61          | ~ (m1_pre_topc @ X13 @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 9.42/9.61          | (m1_pre_topc @ X13 @ X12)
% 9.42/9.61          | ~ (l1_pre_topc @ X13))),
% 9.42/9.61      inference('cnf', [status(esa)], [t65_pre_topc])).
% 9.42/9.61  thf('39', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.61          | ~ (l1_pre_topc @ 
% 9.42/9.61               (g1_pre_topc @ 
% 9.42/9.61                (u1_struct_0 @ 
% 9.42/9.61                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 9.42/9.61                (u1_pre_topc @ 
% 9.42/9.61                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 9.42/9.61          | (m1_pre_topc @ 
% 9.42/9.61             (g1_pre_topc @ 
% 9.42/9.61              (u1_struct_0 @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 9.42/9.61              (u1_pre_topc @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 9.42/9.61             X0)
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('sup-', [status(thm)], ['37', '38'])).
% 9.42/9.61  thf('40', plain,
% 9.42/9.61      ((~ (l1_pre_topc @ sk_B_1)
% 9.42/9.61        | (m1_pre_topc @ 
% 9.42/9.61           (g1_pre_topc @ 
% 9.42/9.61            (u1_struct_0 @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))) @ 
% 9.42/9.61            (u1_pre_topc @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) @ 
% 9.42/9.61           sk_B_1)
% 9.42/9.61        | ~ (l1_pre_topc @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 9.42/9.61      inference('sup-', [status(thm)], ['36', '39'])).
% 9.42/9.61  thf('41', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 9.42/9.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.61  thf('42', plain,
% 9.42/9.61      (![X5 : $i, X6 : $i]:
% 9.42/9.61         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 9.42/9.61      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 9.42/9.61  thf('43', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 9.42/9.61      inference('sup-', [status(thm)], ['41', '42'])).
% 9.42/9.61  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 9.42/9.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.61  thf('45', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.61  thf('46', plain,
% 9.42/9.61      ((m1_pre_topc @ 
% 9.42/9.61        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)) @ sk_A)),
% 9.42/9.61      inference('demod', [status(thm)], ['26', '27'])).
% 9.42/9.61  thf('47', plain,
% 9.42/9.61      (![X5 : $i, X6 : $i]:
% 9.42/9.61         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 9.42/9.61      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 9.42/9.61  thf('48', plain,
% 9.42/9.61      ((~ (l1_pre_topc @ sk_A)
% 9.42/9.61        | (l1_pre_topc @ 
% 9.42/9.61           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 9.42/9.61      inference('sup-', [status(thm)], ['46', '47'])).
% 9.42/9.61  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 9.42/9.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.61  thf('50', plain,
% 9.42/9.61      ((l1_pre_topc @ 
% 9.42/9.61        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 9.42/9.61      inference('demod', [status(thm)], ['48', '49'])).
% 9.42/9.61  thf('51', plain,
% 9.42/9.61      ((m1_pre_topc @ 
% 9.42/9.61        (g1_pre_topc @ 
% 9.42/9.61         (u1_struct_0 @ 
% 9.42/9.61          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))) @ 
% 9.42/9.61         (u1_pre_topc @ 
% 9.42/9.61          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) @ 
% 9.42/9.61        sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['40', '45', '50'])).
% 9.42/9.61  thf('52', plain,
% 9.42/9.61      (![X19 : $i, X20 : $i]:
% 9.42/9.61         (~ (m1_pre_topc @ X19 @ X20)
% 9.42/9.61          | (r1_tarski @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 9.42/9.61          | ~ (l1_pre_topc @ X20))),
% 9.42/9.61      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 9.42/9.61  thf('53', plain,
% 9.42/9.61      ((~ (l1_pre_topc @ sk_B_1)
% 9.42/9.61        | (r1_tarski @ 
% 9.42/9.61           (u1_struct_0 @ 
% 9.42/9.61            (g1_pre_topc @ 
% 9.42/9.61             (u1_struct_0 @ 
% 9.42/9.61              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))) @ 
% 9.42/9.61             (u1_pre_topc @ 
% 9.42/9.61              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))) @ 
% 9.42/9.61           (u1_struct_0 @ sk_B_1)))),
% 9.42/9.61      inference('sup-', [status(thm)], ['51', '52'])).
% 9.42/9.61  thf('54', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.61  thf('55', plain,
% 9.42/9.61      ((r1_tarski @ 
% 9.42/9.61        (u1_struct_0 @ 
% 9.42/9.61         (g1_pre_topc @ 
% 9.42/9.61          (u1_struct_0 @ 
% 9.42/9.61           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))) @ 
% 9.42/9.61          (u1_pre_topc @ 
% 9.42/9.61           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))) @ 
% 9.42/9.61        (u1_struct_0 @ sk_B_1))),
% 9.42/9.61      inference('demod', [status(thm)], ['53', '54'])).
% 9.42/9.61  thf('56', plain,
% 9.42/9.61      (((r1_tarski @ 
% 9.42/9.61         (u1_struct_0 @ 
% 9.42/9.61          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))) @ 
% 9.42/9.61         (u1_struct_0 @ sk_B_1))
% 9.42/9.61        | ~ (l1_pre_topc @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 9.42/9.61      inference('sup+', [status(thm)], ['23', '55'])).
% 9.42/9.61  thf('57', plain,
% 9.42/9.61      ((l1_pre_topc @ 
% 9.42/9.61        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 9.42/9.61      inference('demod', [status(thm)], ['48', '49'])).
% 9.42/9.61  thf('58', plain,
% 9.42/9.61      ((r1_tarski @ 
% 9.42/9.61        (u1_struct_0 @ 
% 9.42/9.61         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))) @ 
% 9.42/9.61        (u1_struct_0 @ sk_B_1))),
% 9.42/9.61      inference('demod', [status(thm)], ['56', '57'])).
% 9.42/9.61  thf('59', plain,
% 9.42/9.61      (![X0 : $i, X2 : $i]:
% 9.42/9.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.42/9.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.42/9.61  thf('60', plain,
% 9.42/9.61      ((~ (r1_tarski @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.61           (u1_struct_0 @ 
% 9.42/9.61            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 9.42/9.61        | ((u1_struct_0 @ sk_B_1)
% 9.42/9.61            = (u1_struct_0 @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 9.42/9.61      inference('sup-', [status(thm)], ['58', '59'])).
% 9.42/9.61  thf('61', plain,
% 9.42/9.61      ((~ (l1_pre_topc @ sk_B_1)
% 9.42/9.61        | ((u1_struct_0 @ sk_B_1)
% 9.42/9.61            = (u1_struct_0 @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 9.42/9.61      inference('sup-', [status(thm)], ['14', '60'])).
% 9.42/9.61  thf('62', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.61  thf('63', plain,
% 9.42/9.61      (((u1_struct_0 @ sk_B_1)
% 9.42/9.61         = (u1_struct_0 @ 
% 9.42/9.61            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 9.42/9.61      inference('demod', [status(thm)], ['61', '62'])).
% 9.42/9.61  thf(d1_tex_1, axiom,
% 9.42/9.61    (![A:$i]:
% 9.42/9.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 9.42/9.61       ( ( v7_struct_0 @ A ) <=>
% 9.42/9.61         ( ?[B:$i]:
% 9.42/9.61           ( ( ( u1_struct_0 @ A ) = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) & 
% 9.42/9.61             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 9.42/9.61  thf('64', plain,
% 9.42/9.61      (![X21 : $i]:
% 9.42/9.61         (~ (v7_struct_0 @ X21)
% 9.42/9.61          | ((u1_struct_0 @ X21)
% 9.42/9.61              = (k6_domain_1 @ (u1_struct_0 @ X21) @ (sk_B @ X21)))
% 9.42/9.61          | ~ (l1_struct_0 @ X21)
% 9.42/9.61          | (v2_struct_0 @ X21))),
% 9.42/9.61      inference('cnf', [status(esa)], [d1_tex_1])).
% 9.42/9.61  thf('65', plain,
% 9.42/9.61      (((u1_struct_0 @ sk_B_1)
% 9.42/9.61         = (u1_struct_0 @ 
% 9.42/9.61            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 9.42/9.61      inference('demod', [status(thm)], ['61', '62'])).
% 9.42/9.61  thf('66', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         ((m1_pre_topc @ X0 @ 
% 9.42/9.61           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('simplify', [status(thm)], ['3'])).
% 9.42/9.61  thf('67', plain,
% 9.42/9.61      (![X12 : $i, X13 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X12)
% 9.42/9.61          | ~ (m1_pre_topc @ X13 @ X12)
% 9.42/9.61          | (m1_pre_topc @ X13 @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 9.42/9.61          | ~ (l1_pre_topc @ X13))),
% 9.42/9.61      inference('cnf', [status(esa)], [t65_pre_topc])).
% 9.42/9.61  thf('68', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X0)
% 9.42/9.61          | ~ (l1_pre_topc @ X0)
% 9.42/9.61          | (m1_pre_topc @ X0 @ 
% 9.42/9.61             (g1_pre_topc @ 
% 9.42/9.61              (u1_struct_0 @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 9.42/9.61              (u1_pre_topc @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 9.42/9.61          | ~ (l1_pre_topc @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 9.42/9.61      inference('sup-', [status(thm)], ['66', '67'])).
% 9.42/9.61  thf('69', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.61          | (m1_pre_topc @ X0 @ 
% 9.42/9.61             (g1_pre_topc @ 
% 9.42/9.61              (u1_struct_0 @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 9.42/9.61              (u1_pre_topc @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('simplify', [status(thm)], ['68'])).
% 9.42/9.61  thf('70', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         ((l1_pre_topc @ 
% 9.42/9.61           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('simplify', [status(thm)], ['12'])).
% 9.42/9.61  thf('71', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X0)
% 9.42/9.61          | (m1_pre_topc @ X0 @ 
% 9.42/9.61             (g1_pre_topc @ 
% 9.42/9.61              (u1_struct_0 @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 9.42/9.61              (u1_pre_topc @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))),
% 9.42/9.61      inference('clc', [status(thm)], ['69', '70'])).
% 9.42/9.61  thf('72', plain,
% 9.42/9.61      (((m1_pre_topc @ sk_B_1 @ 
% 9.42/9.61         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.61          (u1_pre_topc @ 
% 9.42/9.61           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 9.42/9.61        | ~ (l1_pre_topc @ sk_B_1))),
% 9.42/9.61      inference('sup+', [status(thm)], ['65', '71'])).
% 9.42/9.61  thf('73', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.61  thf('74', plain,
% 9.42/9.61      ((m1_pre_topc @ sk_B_1 @ 
% 9.42/9.61        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.61         (u1_pre_topc @ 
% 9.42/9.61          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 9.42/9.61      inference('demod', [status(thm)], ['72', '73'])).
% 9.42/9.61  thf('75', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         (((u1_struct_0 @ X0)
% 9.42/9.61            = (u1_struct_0 @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('simplify', [status(thm)], ['22'])).
% 9.42/9.61  thf('76', plain,
% 9.42/9.61      (![X12 : $i, X13 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X12)
% 9.42/9.61          | ~ (m1_pre_topc @ X13 @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 9.42/9.61          | (m1_pre_topc @ X13 @ X12)
% 9.42/9.61          | ~ (l1_pre_topc @ X13))),
% 9.42/9.61      inference('cnf', [status(esa)], [t65_pre_topc])).
% 9.42/9.61  thf('77', plain,
% 9.42/9.61      (![X0 : $i, X1 : $i]:
% 9.42/9.61         (~ (m1_pre_topc @ X1 @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 9.42/9.61              (u1_pre_topc @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 9.42/9.61          | ~ (l1_pre_topc @ X0)
% 9.42/9.61          | ~ (l1_pre_topc @ X1)
% 9.42/9.61          | (m1_pre_topc @ X1 @ 
% 9.42/9.61             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.61          | ~ (l1_pre_topc @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 9.42/9.61      inference('sup-', [status(thm)], ['75', '76'])).
% 9.42/9.61  thf('78', plain,
% 9.42/9.61      ((~ (l1_pre_topc @ 
% 9.42/9.61           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 9.42/9.61        | (m1_pre_topc @ sk_B_1 @ 
% 9.42/9.61           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 9.42/9.61        | ~ (l1_pre_topc @ sk_B_1)
% 9.42/9.61        | ~ (l1_pre_topc @ sk_B_1))),
% 9.42/9.61      inference('sup-', [status(thm)], ['74', '77'])).
% 9.42/9.61  thf('79', plain,
% 9.42/9.61      ((l1_pre_topc @ 
% 9.42/9.61        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 9.42/9.61      inference('demod', [status(thm)], ['48', '49'])).
% 9.42/9.61  thf('80', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.61  thf('81', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.61  thf('82', plain,
% 9.42/9.61      ((m1_pre_topc @ sk_B_1 @ 
% 9.42/9.61        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 9.42/9.61      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 9.42/9.61  thf('83', plain,
% 9.42/9.61      (![X12 : $i, X13 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X12)
% 9.42/9.61          | ~ (m1_pre_topc @ X13 @ 
% 9.42/9.61               (g1_pre_topc @ (u1_struct_0 @ X12) @ (u1_pre_topc @ X12)))
% 9.42/9.61          | (m1_pre_topc @ X13 @ X12)
% 9.42/9.61          | ~ (l1_pre_topc @ X13))),
% 9.42/9.61      inference('cnf', [status(esa)], [t65_pre_topc])).
% 9.42/9.61  thf('84', plain,
% 9.42/9.61      ((~ (l1_pre_topc @ sk_B_1)
% 9.42/9.61        | (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 9.42/9.61        | ~ (l1_pre_topc @ sk_B_1))),
% 9.42/9.61      inference('sup-', [status(thm)], ['82', '83'])).
% 9.42/9.61  thf('85', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.61  thf('86', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.61  thf('87', plain, ((m1_pre_topc @ sk_B_1 @ sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['84', '85', '86'])).
% 9.42/9.61  thf('88', plain,
% 9.42/9.61      (![X21 : $i]:
% 9.42/9.61         (~ (v7_struct_0 @ X21)
% 9.42/9.61          | (m1_subset_1 @ (sk_B @ X21) @ (u1_struct_0 @ X21))
% 9.42/9.61          | ~ (l1_struct_0 @ X21)
% 9.42/9.61          | (v2_struct_0 @ X21))),
% 9.42/9.61      inference('cnf', [status(esa)], [d1_tex_1])).
% 9.42/9.61  thf(t55_pre_topc, axiom,
% 9.42/9.61    (![A:$i]:
% 9.42/9.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 9.42/9.61       ( ![B:$i]:
% 9.42/9.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 9.42/9.61           ( ![C:$i]:
% 9.42/9.61             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 9.42/9.61               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 9.42/9.61  thf('89', plain,
% 9.42/9.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 9.42/9.61         ((v2_struct_0 @ X9)
% 9.42/9.61          | ~ (m1_pre_topc @ X9 @ X10)
% 9.42/9.61          | (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 9.42/9.61          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 9.42/9.61          | ~ (l1_pre_topc @ X10)
% 9.42/9.61          | (v2_struct_0 @ X10))),
% 9.42/9.61      inference('cnf', [status(esa)], [t55_pre_topc])).
% 9.42/9.61  thf('90', plain,
% 9.42/9.61      (![X0 : $i, X1 : $i]:
% 9.42/9.61         ((v2_struct_0 @ X0)
% 9.42/9.61          | ~ (l1_struct_0 @ X0)
% 9.42/9.61          | ~ (v7_struct_0 @ X0)
% 9.42/9.61          | (v2_struct_0 @ X1)
% 9.42/9.61          | ~ (l1_pre_topc @ X1)
% 9.42/9.61          | (m1_subset_1 @ (sk_B @ X0) @ (u1_struct_0 @ X1))
% 9.42/9.61          | ~ (m1_pre_topc @ X0 @ X1)
% 9.42/9.61          | (v2_struct_0 @ X0))),
% 9.42/9.61      inference('sup-', [status(thm)], ['88', '89'])).
% 9.42/9.61  thf('91', plain,
% 9.42/9.61      (![X0 : $i, X1 : $i]:
% 9.42/9.61         (~ (m1_pre_topc @ X0 @ X1)
% 9.42/9.61          | (m1_subset_1 @ (sk_B @ X0) @ (u1_struct_0 @ X1))
% 9.42/9.61          | ~ (l1_pre_topc @ X1)
% 9.42/9.61          | (v2_struct_0 @ X1)
% 9.42/9.61          | ~ (v7_struct_0 @ X0)
% 9.42/9.61          | ~ (l1_struct_0 @ X0)
% 9.42/9.61          | (v2_struct_0 @ X0))),
% 9.42/9.61      inference('simplify', [status(thm)], ['90'])).
% 9.42/9.61  thf('92', plain,
% 9.42/9.61      (((v2_struct_0 @ sk_B_1)
% 9.42/9.61        | ~ (l1_struct_0 @ sk_B_1)
% 9.42/9.61        | ~ (v7_struct_0 @ sk_B_1)
% 9.42/9.61        | (v2_struct_0 @ sk_B_1)
% 9.42/9.61        | ~ (l1_pre_topc @ sk_B_1)
% 9.42/9.61        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_B_1)))),
% 9.42/9.61      inference('sup-', [status(thm)], ['87', '91'])).
% 9.42/9.61  thf('93', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.61  thf(dt_l1_pre_topc, axiom,
% 9.42/9.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 9.42/9.61  thf('94', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 9.42/9.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 9.42/9.61  thf('95', plain, ((l1_struct_0 @ sk_B_1)),
% 9.42/9.61      inference('sup-', [status(thm)], ['93', '94'])).
% 9.42/9.61  thf('96', plain, ((v7_struct_0 @ sk_B_1)),
% 9.42/9.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.61  thf('97', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.61  thf('98', plain,
% 9.42/9.61      (((v2_struct_0 @ sk_B_1)
% 9.42/9.61        | (v2_struct_0 @ sk_B_1)
% 9.42/9.61        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_B_1)))),
% 9.42/9.61      inference('demod', [status(thm)], ['92', '95', '96', '97'])).
% 9.42/9.61  thf('99', plain,
% 9.42/9.61      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_B_1))
% 9.42/9.61        | (v2_struct_0 @ sk_B_1))),
% 9.42/9.61      inference('simplify', [status(thm)], ['98'])).
% 9.42/9.61  thf('100', plain, (~ (v2_struct_0 @ sk_B_1)),
% 9.42/9.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.61  thf('101', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_B_1))),
% 9.42/9.61      inference('clc', [status(thm)], ['99', '100'])).
% 9.42/9.61  thf(dt_k1_tex_2, axiom,
% 9.42/9.61    (![A:$i,B:$i]:
% 9.42/9.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 9.42/9.61         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 9.42/9.61       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 9.42/9.61         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 9.42/9.61         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 9.42/9.61  thf('102', plain,
% 9.42/9.61      (![X26 : $i, X27 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X26)
% 9.42/9.61          | (v2_struct_0 @ X26)
% 9.42/9.61          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 9.42/9.61          | (m1_pre_topc @ (k1_tex_2 @ X26 @ X27) @ X26))),
% 9.42/9.61      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 9.42/9.61  thf('103', plain,
% 9.42/9.61      (((m1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)) @ sk_B_1)
% 9.42/9.61        | (v2_struct_0 @ sk_B_1)
% 9.42/9.61        | ~ (l1_pre_topc @ sk_B_1))),
% 9.42/9.61      inference('sup-', [status(thm)], ['101', '102'])).
% 9.42/9.61  thf('104', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.61  thf('105', plain,
% 9.42/9.61      (((m1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)) @ sk_B_1)
% 9.42/9.61        | (v2_struct_0 @ sk_B_1))),
% 9.42/9.61      inference('demod', [status(thm)], ['103', '104'])).
% 9.42/9.61  thf('106', plain, (~ (v2_struct_0 @ sk_B_1)),
% 9.42/9.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.61  thf('107', plain,
% 9.42/9.61      ((m1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)) @ sk_B_1)),
% 9.42/9.61      inference('clc', [status(thm)], ['105', '106'])).
% 9.42/9.61  thf('108', plain,
% 9.42/9.61      (![X19 : $i, X20 : $i]:
% 9.42/9.61         (~ (m1_pre_topc @ X19 @ X20)
% 9.42/9.61          | (r1_tarski @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X20))
% 9.42/9.61          | ~ (l1_pre_topc @ X20))),
% 9.42/9.61      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 9.42/9.61  thf('109', plain,
% 9.42/9.61      ((~ (l1_pre_topc @ sk_B_1)
% 9.42/9.61        | (r1_tarski @ (u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))) @ 
% 9.42/9.61           (u1_struct_0 @ sk_B_1)))),
% 9.42/9.61      inference('sup-', [status(thm)], ['107', '108'])).
% 9.42/9.61  thf('110', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.61  thf('111', plain,
% 9.42/9.61      ((r1_tarski @ (u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))) @ 
% 9.42/9.61        (u1_struct_0 @ sk_B_1))),
% 9.42/9.61      inference('demod', [status(thm)], ['109', '110'])).
% 9.42/9.61  thf('112', plain,
% 9.42/9.61      (![X0 : $i, X2 : $i]:
% 9.42/9.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 9.42/9.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.42/9.61  thf('113', plain,
% 9.42/9.61      ((~ (r1_tarski @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.61           (u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))
% 9.42/9.61        | ((u1_struct_0 @ sk_B_1)
% 9.42/9.61            = (u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))),
% 9.42/9.61      inference('sup-', [status(thm)], ['111', '112'])).
% 9.42/9.61  thf('114', plain,
% 9.42/9.61      ((m1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)) @ sk_B_1)),
% 9.42/9.61      inference('clc', [status(thm)], ['105', '106'])).
% 9.42/9.61  thf('115', plain,
% 9.42/9.61      (![X21 : $i]:
% 9.42/9.61         (~ (v7_struct_0 @ X21)
% 9.42/9.61          | (m1_subset_1 @ (sk_B @ X21) @ (u1_struct_0 @ X21))
% 9.42/9.61          | ~ (l1_struct_0 @ X21)
% 9.42/9.61          | (v2_struct_0 @ X21))),
% 9.42/9.61      inference('cnf', [status(esa)], [d1_tex_1])).
% 9.42/9.61  thf('116', plain,
% 9.42/9.61      (![X26 : $i, X27 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X26)
% 9.42/9.61          | (v2_struct_0 @ X26)
% 9.42/9.61          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 9.42/9.61          | (v1_pre_topc @ (k1_tex_2 @ X26 @ X27)))),
% 9.42/9.61      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 9.42/9.61  thf('117', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         ((v2_struct_0 @ X0)
% 9.42/9.61          | ~ (l1_struct_0 @ X0)
% 9.42/9.61          | ~ (v7_struct_0 @ X0)
% 9.42/9.61          | (v1_pre_topc @ (k1_tex_2 @ X0 @ (sk_B @ X0)))
% 9.42/9.61          | (v2_struct_0 @ X0)
% 9.42/9.61          | ~ (l1_pre_topc @ X0))),
% 9.42/9.61      inference('sup-', [status(thm)], ['115', '116'])).
% 9.42/9.61  thf('118', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X0)
% 9.42/9.61          | (v1_pre_topc @ (k1_tex_2 @ X0 @ (sk_B @ X0)))
% 9.42/9.61          | ~ (v7_struct_0 @ X0)
% 9.42/9.61          | ~ (l1_struct_0 @ X0)
% 9.42/9.61          | (v2_struct_0 @ X0))),
% 9.42/9.61      inference('simplify', [status(thm)], ['117'])).
% 9.42/9.61  thf(d4_tex_2, axiom,
% 9.42/9.61    (![A:$i]:
% 9.42/9.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 9.42/9.61       ( ![B:$i]:
% 9.42/9.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 9.42/9.61           ( ![C:$i]:
% 9.42/9.61             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 9.42/9.61                 ( m1_pre_topc @ C @ A ) ) =>
% 9.42/9.61               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 9.42/9.61                 ( ( u1_struct_0 @ C ) =
% 9.42/9.61                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 9.42/9.61  thf('119', plain,
% 9.42/9.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 9.42/9.61         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 9.42/9.61          | ((X25) != (k1_tex_2 @ X24 @ X23))
% 9.42/9.61          | ((u1_struct_0 @ X25) = (k6_domain_1 @ (u1_struct_0 @ X24) @ X23))
% 9.42/9.61          | ~ (m1_pre_topc @ X25 @ X24)
% 9.42/9.61          | ~ (v1_pre_topc @ X25)
% 9.42/9.61          | (v2_struct_0 @ X25)
% 9.42/9.61          | ~ (l1_pre_topc @ X24)
% 9.42/9.61          | (v2_struct_0 @ X24))),
% 9.42/9.61      inference('cnf', [status(esa)], [d4_tex_2])).
% 9.42/9.61  thf('120', plain,
% 9.42/9.61      (![X23 : $i, X24 : $i]:
% 9.42/9.61         ((v2_struct_0 @ X24)
% 9.42/9.61          | ~ (l1_pre_topc @ X24)
% 9.42/9.61          | (v2_struct_0 @ (k1_tex_2 @ X24 @ X23))
% 9.42/9.61          | ~ (v1_pre_topc @ (k1_tex_2 @ X24 @ X23))
% 9.42/9.61          | ~ (m1_pre_topc @ (k1_tex_2 @ X24 @ X23) @ X24)
% 9.42/9.61          | ((u1_struct_0 @ (k1_tex_2 @ X24 @ X23))
% 9.42/9.61              = (k6_domain_1 @ (u1_struct_0 @ X24) @ X23))
% 9.42/9.61          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24)))),
% 9.42/9.61      inference('simplify', [status(thm)], ['119'])).
% 9.42/9.61  thf('121', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         ((v2_struct_0 @ X0)
% 9.42/9.61          | ~ (l1_struct_0 @ X0)
% 9.42/9.61          | ~ (v7_struct_0 @ X0)
% 9.42/9.61          | ~ (l1_pre_topc @ X0)
% 9.42/9.61          | ~ (m1_subset_1 @ (sk_B @ X0) @ (u1_struct_0 @ X0))
% 9.42/9.61          | ((u1_struct_0 @ (k1_tex_2 @ X0 @ (sk_B @ X0)))
% 9.42/9.61              = (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ X0)))
% 9.42/9.61          | ~ (m1_pre_topc @ (k1_tex_2 @ X0 @ (sk_B @ X0)) @ X0)
% 9.42/9.61          | (v2_struct_0 @ (k1_tex_2 @ X0 @ (sk_B @ X0)))
% 9.42/9.61          | ~ (l1_pre_topc @ X0)
% 9.42/9.61          | (v2_struct_0 @ X0))),
% 9.42/9.61      inference('sup-', [status(thm)], ['118', '120'])).
% 9.42/9.61  thf('122', plain,
% 9.42/9.61      (![X0 : $i]:
% 9.42/9.61         ((v2_struct_0 @ (k1_tex_2 @ X0 @ (sk_B @ X0)))
% 9.42/9.61          | ~ (m1_pre_topc @ (k1_tex_2 @ X0 @ (sk_B @ X0)) @ X0)
% 9.42/9.61          | ((u1_struct_0 @ (k1_tex_2 @ X0 @ (sk_B @ X0)))
% 9.42/9.61              = (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ X0)))
% 9.42/9.61          | ~ (m1_subset_1 @ (sk_B @ X0) @ (u1_struct_0 @ X0))
% 9.42/9.61          | ~ (l1_pre_topc @ X0)
% 9.42/9.61          | ~ (v7_struct_0 @ X0)
% 9.42/9.61          | ~ (l1_struct_0 @ X0)
% 9.42/9.61          | (v2_struct_0 @ X0))),
% 9.42/9.61      inference('simplify', [status(thm)], ['121'])).
% 9.42/9.61  thf('123', plain,
% 9.42/9.61      (((v2_struct_0 @ sk_B_1)
% 9.42/9.61        | ~ (l1_struct_0 @ sk_B_1)
% 9.42/9.61        | ~ (v7_struct_0 @ sk_B_1)
% 9.42/9.61        | ~ (l1_pre_topc @ sk_B_1)
% 9.42/9.61        | ~ (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_B_1))
% 9.42/9.61        | ((u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.61            = (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)))
% 9.42/9.61        | (v2_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))),
% 9.42/9.61      inference('sup-', [status(thm)], ['114', '122'])).
% 9.42/9.61  thf('124', plain, ((l1_struct_0 @ sk_B_1)),
% 9.42/9.61      inference('sup-', [status(thm)], ['93', '94'])).
% 9.42/9.61  thf('125', plain, ((v7_struct_0 @ sk_B_1)),
% 9.42/9.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.61  thf('126', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.61      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.61  thf('127', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_B_1))),
% 9.42/9.61      inference('clc', [status(thm)], ['99', '100'])).
% 9.42/9.61  thf('128', plain,
% 9.42/9.61      (((v2_struct_0 @ sk_B_1)
% 9.42/9.61        | ((u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.61            = (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)))
% 9.42/9.61        | (v2_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))),
% 9.42/9.61      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 9.42/9.61  thf('129', plain, (~ (v2_struct_0 @ sk_B_1)),
% 9.42/9.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.61  thf('130', plain,
% 9.42/9.61      (((v2_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.61        | ((u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.61            = (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1))))),
% 9.42/9.61      inference('clc', [status(thm)], ['128', '129'])).
% 9.42/9.61  thf('131', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_B_1))),
% 9.42/9.61      inference('clc', [status(thm)], ['99', '100'])).
% 9.42/9.61  thf('132', plain,
% 9.42/9.61      (![X26 : $i, X27 : $i]:
% 9.42/9.61         (~ (l1_pre_topc @ X26)
% 9.42/9.62          | (v2_struct_0 @ X26)
% 9.42/9.62          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 9.42/9.62          | ~ (v2_struct_0 @ (k1_tex_2 @ X26 @ X27)))),
% 9.42/9.62      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 9.42/9.62  thf('133', plain,
% 9.42/9.62      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (l1_pre_topc @ sk_B_1))),
% 9.42/9.62      inference('sup-', [status(thm)], ['131', '132'])).
% 9.42/9.62  thf('134', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.62      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.62  thf('135', plain,
% 9.42/9.62      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('demod', [status(thm)], ['133', '134'])).
% 9.42/9.62  thf('136', plain, (~ (v2_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('137', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['135', '136'])).
% 9.42/9.62  thf('138', plain,
% 9.42/9.62      (((u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62         = (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['130', '137'])).
% 9.42/9.62  thf('139', plain,
% 9.42/9.62      (((u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62         = (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['130', '137'])).
% 9.42/9.62  thf('140', plain,
% 9.42/9.62      ((~ (r1_tarski @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62           (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)))
% 9.42/9.62        | ((u1_struct_0 @ sk_B_1)
% 9.42/9.62            = (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('demod', [status(thm)], ['113', '138', '139'])).
% 9.42/9.62  thf('141', plain,
% 9.42/9.62      ((~ (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_B_1))
% 9.42/9.62        | (v2_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (l1_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (v7_struct_0 @ sk_B_1)
% 9.42/9.62        | ((u1_struct_0 @ sk_B_1)
% 9.42/9.62            = (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('sup-', [status(thm)], ['64', '140'])).
% 9.42/9.62  thf('142', plain,
% 9.42/9.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 9.42/9.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.42/9.62  thf('143', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 9.42/9.62      inference('simplify', [status(thm)], ['142'])).
% 9.42/9.62  thf('144', plain, ((l1_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('sup-', [status(thm)], ['93', '94'])).
% 9.42/9.62  thf('145', plain, ((v7_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('146', plain,
% 9.42/9.62      (((v2_struct_0 @ sk_B_1)
% 9.42/9.62        | ((u1_struct_0 @ sk_B_1)
% 9.42/9.62            = (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('demod', [status(thm)], ['141', '143', '144', '145'])).
% 9.42/9.62  thf('147', plain, (~ (v2_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('148', plain,
% 9.42/9.62      (((u1_struct_0 @ sk_B_1)
% 9.42/9.62         = (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['146', '147'])).
% 9.42/9.62  thf('149', plain,
% 9.42/9.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 9.42/9.62         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 9.42/9.62          | ((u1_struct_0 @ X25) != (k6_domain_1 @ (u1_struct_0 @ X24) @ X23))
% 9.42/9.62          | ((X25) = (k1_tex_2 @ X24 @ X23))
% 9.42/9.62          | ~ (m1_pre_topc @ X25 @ X24)
% 9.42/9.62          | ~ (v1_pre_topc @ X25)
% 9.42/9.62          | (v2_struct_0 @ X25)
% 9.42/9.62          | ~ (l1_pre_topc @ X24)
% 9.42/9.62          | (v2_struct_0 @ X24))),
% 9.42/9.62      inference('cnf', [status(esa)], [d4_tex_2])).
% 9.42/9.62  thf('150', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (((u1_struct_0 @ X0) != (u1_struct_0 @ sk_B_1))
% 9.42/9.62          | (v2_struct_0 @ sk_B_1)
% 9.42/9.62          | ~ (l1_pre_topc @ sk_B_1)
% 9.42/9.62          | (v2_struct_0 @ X0)
% 9.42/9.62          | ~ (v1_pre_topc @ X0)
% 9.42/9.62          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 9.42/9.62          | ((X0) = (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62          | ~ (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_B_1)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['148', '149'])).
% 9.42/9.62  thf('151', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.62      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.62  thf('152', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('clc', [status(thm)], ['99', '100'])).
% 9.42/9.62  thf('153', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (((u1_struct_0 @ X0) != (u1_struct_0 @ sk_B_1))
% 9.42/9.62          | (v2_struct_0 @ sk_B_1)
% 9.42/9.62          | (v2_struct_0 @ X0)
% 9.42/9.62          | ~ (v1_pre_topc @ X0)
% 9.42/9.62          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 9.42/9.62          | ((X0) = (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('demod', [status(thm)], ['150', '151', '152'])).
% 9.42/9.62  thf('154', plain,
% 9.42/9.62      ((((u1_struct_0 @ sk_B_1) != (u1_struct_0 @ sk_B_1))
% 9.42/9.62        | ((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62            = (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62        | ~ (m1_pre_topc @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)) @ 
% 9.42/9.62             sk_B_1)
% 9.42/9.62        | ~ (v1_pre_topc @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('sup-', [status(thm)], ['63', '153'])).
% 9.42/9.62  thf('155', plain, ((m1_pre_topc @ sk_B_1 @ sk_B_1)),
% 9.42/9.62      inference('demod', [status(thm)], ['84', '85', '86'])).
% 9.42/9.62  thf('156', plain,
% 9.42/9.62      (![X16 : $i, X17 : $i]:
% 9.42/9.62         (~ (m1_pre_topc @ X16 @ X17)
% 9.42/9.62          | (m1_pre_topc @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)) @ X17)
% 9.42/9.62          | ~ (l1_pre_topc @ X17))),
% 9.42/9.62      inference('cnf', [status(esa)], [t11_tmap_1])).
% 9.42/9.62  thf('157', plain,
% 9.42/9.62      ((~ (l1_pre_topc @ sk_B_1)
% 9.42/9.62        | (m1_pre_topc @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)) @ 
% 9.42/9.62           sk_B_1))),
% 9.42/9.62      inference('sup-', [status(thm)], ['155', '156'])).
% 9.42/9.62  thf('158', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.62      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.62  thf('159', plain,
% 9.42/9.62      ((m1_pre_topc @ 
% 9.42/9.62        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)) @ 
% 9.42/9.62        sk_B_1)),
% 9.42/9.62      inference('demod', [status(thm)], ['157', '158'])).
% 9.42/9.62  thf('160', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('161', plain,
% 9.42/9.62      (![X16 : $i, X17 : $i]:
% 9.42/9.62         (~ (m1_pre_topc @ X16 @ X17)
% 9.42/9.62          | (v1_pre_topc @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 9.42/9.62          | ~ (l1_pre_topc @ X17))),
% 9.42/9.62      inference('cnf', [status(esa)], [t11_tmap_1])).
% 9.42/9.62  thf('162', plain,
% 9.42/9.62      ((~ (l1_pre_topc @ sk_A)
% 9.42/9.62        | (v1_pre_topc @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 9.42/9.62      inference('sup-', [status(thm)], ['160', '161'])).
% 9.42/9.62  thf('163', plain, ((l1_pre_topc @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('164', plain,
% 9.42/9.62      ((v1_pre_topc @ 
% 9.42/9.62        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 9.42/9.62      inference('demod', [status(thm)], ['162', '163'])).
% 9.42/9.62  thf('165', plain,
% 9.42/9.62      ((((u1_struct_0 @ sk_B_1) != (u1_struct_0 @ sk_B_1))
% 9.42/9.62        | ((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62            = (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('demod', [status(thm)], ['154', '159', '164'])).
% 9.42/9.62  thf('166', plain,
% 9.42/9.62      (((v2_struct_0 @ sk_B_1)
% 9.42/9.62        | (v2_struct_0 @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 9.42/9.62        | ((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62            = (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('simplify', [status(thm)], ['165'])).
% 9.42/9.62  thf('167', plain, (~ (v2_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('168', plain,
% 9.42/9.62      ((((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62          = (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 9.42/9.62      inference('clc', [status(thm)], ['166', '167'])).
% 9.42/9.62  thf('169', plain,
% 9.42/9.62      ((l1_pre_topc @ 
% 9.42/9.62        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 9.42/9.62      inference('demod', [status(thm)], ['48', '49'])).
% 9.42/9.62  thf('170', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (((u1_struct_0 @ X0)
% 9.42/9.62            = (u1_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['22'])).
% 9.42/9.62  thf('171', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         ((l1_pre_topc @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['12'])).
% 9.42/9.62  thf('172', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         ((l1_pre_topc @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['12'])).
% 9.42/9.62  thf('173', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 9.42/9.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 9.42/9.62  thf('174', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (l1_pre_topc @ X0)
% 9.42/9.62          | (l1_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 9.42/9.62      inference('sup-', [status(thm)], ['172', '173'])).
% 9.42/9.62  thf(fc1_struct_0, axiom,
% 9.42/9.62    (![A:$i]:
% 9.42/9.62     ( ( ( v2_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 9.42/9.62       ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ))).
% 9.42/9.62  thf('175', plain,
% 9.42/9.62      (![X7 : $i]:
% 9.42/9.62         ((v1_xboole_0 @ (u1_struct_0 @ X7))
% 9.42/9.62          | ~ (l1_struct_0 @ X7)
% 9.42/9.62          | ~ (v2_struct_0 @ X7))),
% 9.42/9.62      inference('cnf', [status(esa)], [fc1_struct_0])).
% 9.42/9.62  thf('176', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         ((l1_pre_topc @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['12'])).
% 9.42/9.62  thf('177', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (((u1_struct_0 @ X0)
% 9.42/9.62            = (u1_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['22'])).
% 9.42/9.62  thf('178', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (l1_pre_topc @ X0)
% 9.42/9.62          | (l1_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 9.42/9.62      inference('sup-', [status(thm)], ['172', '173'])).
% 9.42/9.62  thf('179', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (((u1_struct_0 @ X0)
% 9.42/9.62            = (u1_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['22'])).
% 9.42/9.62  thf(fc2_struct_0, axiom,
% 9.42/9.62    (![A:$i]:
% 9.42/9.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 9.42/9.62       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 9.42/9.62  thf('180', plain,
% 9.42/9.62      (![X8 : $i]:
% 9.42/9.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 9.42/9.62          | ~ (l1_struct_0 @ X8)
% 9.42/9.62          | (v2_struct_0 @ X8))),
% 9.42/9.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 9.42/9.62  thf('181', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 9.42/9.62          | ~ (l1_pre_topc @ X0)
% 9.42/9.62          | (v2_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.62          | ~ (l1_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 9.42/9.62      inference('sup-', [status(thm)], ['179', '180'])).
% 9.42/9.62  thf('182', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (l1_pre_topc @ X0)
% 9.42/9.62          | (v2_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.62          | ~ (l1_pre_topc @ X0)
% 9.42/9.62          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['178', '181'])).
% 9.42/9.62  thf('183', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 9.42/9.62          | (v2_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['182'])).
% 9.42/9.62  thf('184', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 9.42/9.62          | ~ (l1_pre_topc @ X0)
% 9.42/9.62          | ~ (l1_pre_topc @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.62          | (v2_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ 
% 9.42/9.62              (u1_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 9.42/9.62              (u1_pre_topc @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))),
% 9.42/9.62      inference('sup-', [status(thm)], ['177', '183'])).
% 9.42/9.62  thf('185', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (l1_pre_topc @ X0)
% 9.42/9.62          | (v2_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ 
% 9.42/9.62              (u1_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 9.42/9.62              (u1_pre_topc @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 9.42/9.62          | ~ (l1_pre_topc @ X0)
% 9.42/9.62          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['176', '184'])).
% 9.42/9.62  thf('186', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 9.42/9.62          | (v2_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ 
% 9.42/9.62              (u1_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 9.42/9.62              (u1_pre_topc @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['185'])).
% 9.42/9.62  thf('187', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (v2_struct_0 @ X0)
% 9.42/9.62          | ~ (l1_struct_0 @ X0)
% 9.42/9.62          | ~ (l1_pre_topc @ X0)
% 9.42/9.62          | (v2_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ 
% 9.42/9.62              (u1_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 9.42/9.62              (u1_pre_topc @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))),
% 9.42/9.62      inference('sup-', [status(thm)], ['175', '186'])).
% 9.42/9.62  thf('188', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (((u1_struct_0 @ X0)
% 9.42/9.62            = (u1_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['22'])).
% 9.42/9.62  thf('189', plain,
% 9.42/9.62      (![X7 : $i]:
% 9.42/9.62         ((v1_xboole_0 @ (u1_struct_0 @ X7))
% 9.42/9.62          | ~ (l1_struct_0 @ X7)
% 9.42/9.62          | ~ (v2_struct_0 @ X7))),
% 9.42/9.62      inference('cnf', [status(esa)], [fc1_struct_0])).
% 9.42/9.62  thf('190', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 9.42/9.62          | ~ (l1_pre_topc @ X0)
% 9.42/9.62          | ~ (v2_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.62          | ~ (l1_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 9.42/9.62      inference('sup+', [status(thm)], ['188', '189'])).
% 9.42/9.62  thf('191', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (l1_pre_topc @ X0)
% 9.42/9.62          | ~ (l1_struct_0 @ X0)
% 9.42/9.62          | ~ (v2_struct_0 @ X0)
% 9.42/9.62          | ~ (l1_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ 
% 9.42/9.62                (u1_struct_0 @ 
% 9.42/9.62                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 9.42/9.62                (u1_pre_topc @ 
% 9.42/9.62                 (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 9.42/9.62          | ~ (l1_pre_topc @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.62          | (v1_xboole_0 @ 
% 9.42/9.62             (u1_struct_0 @ 
% 9.42/9.62              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))),
% 9.42/9.62      inference('sup-', [status(thm)], ['187', '190'])).
% 9.42/9.62  thf('192', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (l1_pre_topc @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.62          | (v1_xboole_0 @ 
% 9.42/9.62             (u1_struct_0 @ 
% 9.42/9.62              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.62          | ~ (l1_pre_topc @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.62          | ~ (v2_struct_0 @ X0)
% 9.42/9.62          | ~ (l1_struct_0 @ X0)
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('sup-', [status(thm)], ['174', '191'])).
% 9.42/9.62  thf('193', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (l1_pre_topc @ X0)
% 9.42/9.62          | ~ (l1_struct_0 @ X0)
% 9.42/9.62          | ~ (v2_struct_0 @ X0)
% 9.42/9.62          | (v1_xboole_0 @ 
% 9.42/9.62             (u1_struct_0 @ 
% 9.42/9.62              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.62          | ~ (l1_pre_topc @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 9.42/9.62      inference('simplify', [status(thm)], ['192'])).
% 9.42/9.62  thf('194', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (l1_pre_topc @ X0)
% 9.42/9.62          | (v1_xboole_0 @ 
% 9.42/9.62             (u1_struct_0 @ 
% 9.42/9.62              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.62          | ~ (v2_struct_0 @ X0)
% 9.42/9.62          | ~ (l1_struct_0 @ X0)
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('sup-', [status(thm)], ['171', '193'])).
% 9.42/9.62  thf('195', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (l1_struct_0 @ X0)
% 9.42/9.62          | ~ (v2_struct_0 @ X0)
% 9.42/9.62          | (v1_xboole_0 @ 
% 9.42/9.62             (u1_struct_0 @ 
% 9.42/9.62              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['194'])).
% 9.42/9.62  thf('196', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         ((v1_xboole_0 @ 
% 9.42/9.62           (u1_struct_0 @ 
% 9.42/9.62            (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 9.42/9.62             (u1_pre_topc @ 
% 9.42/9.62              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 9.42/9.62          | ~ (l1_pre_topc @ X0)
% 9.42/9.62          | ~ (l1_pre_topc @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.62          | ~ (v2_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 9.42/9.62          | ~ (l1_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 9.42/9.62      inference('sup+', [status(thm)], ['170', '195'])).
% 9.42/9.62  thf('197', plain,
% 9.42/9.62      ((~ (l1_struct_0 @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 9.42/9.62        | ~ (v2_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 9.42/9.62        | ~ (l1_pre_topc @ sk_B_1)
% 9.42/9.62        | (v1_xboole_0 @ 
% 9.42/9.62           (u1_struct_0 @ 
% 9.42/9.62            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62             (u1_pre_topc @ 
% 9.42/9.62              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))))),
% 9.42/9.62      inference('sup-', [status(thm)], ['169', '196'])).
% 9.42/9.62  thf('198', plain,
% 9.42/9.62      ((l1_pre_topc @ 
% 9.42/9.62        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 9.42/9.62      inference('demod', [status(thm)], ['48', '49'])).
% 9.42/9.62  thf('199', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 9.42/9.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 9.42/9.62  thf('200', plain,
% 9.42/9.62      ((l1_struct_0 @ 
% 9.42/9.62        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['198', '199'])).
% 9.42/9.62  thf('201', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.62      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.62  thf('202', plain,
% 9.42/9.62      (((u1_struct_0 @ sk_B_1)
% 9.42/9.62         = (u1_struct_0 @ 
% 9.42/9.62            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 9.42/9.62      inference('demod', [status(thm)], ['61', '62'])).
% 9.42/9.62  thf('203', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (((u1_struct_0 @ X0)
% 9.42/9.62            = (u1_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['22'])).
% 9.42/9.62  thf('204', plain,
% 9.42/9.62      ((((u1_struct_0 @ 
% 9.42/9.62          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 9.42/9.62          = (u1_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62              (u1_pre_topc @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 9.42/9.62        | ~ (l1_pre_topc @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 9.42/9.62      inference('sup+', [status(thm)], ['202', '203'])).
% 9.42/9.62  thf('205', plain,
% 9.42/9.62      (((u1_struct_0 @ sk_B_1)
% 9.42/9.62         = (u1_struct_0 @ 
% 9.42/9.62            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 9.42/9.62      inference('demod', [status(thm)], ['61', '62'])).
% 9.42/9.62  thf('206', plain,
% 9.42/9.62      ((l1_pre_topc @ 
% 9.42/9.62        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 9.42/9.62      inference('demod', [status(thm)], ['48', '49'])).
% 9.42/9.62  thf('207', plain,
% 9.42/9.62      (((u1_struct_0 @ sk_B_1)
% 9.42/9.62         = (u1_struct_0 @ 
% 9.42/9.62            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62             (u1_pre_topc @ 
% 9.42/9.62              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 9.42/9.62      inference('demod', [status(thm)], ['204', '205', '206'])).
% 9.42/9.62  thf('208', plain,
% 9.42/9.62      ((~ (v2_struct_0 @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 9.42/9.62      inference('demod', [status(thm)], ['197', '200', '201', '207'])).
% 9.42/9.62  thf('209', plain,
% 9.42/9.62      (![X21 : $i]:
% 9.42/9.62         (~ (v7_struct_0 @ X21)
% 9.42/9.62          | ((u1_struct_0 @ X21)
% 9.42/9.62              = (k6_domain_1 @ (u1_struct_0 @ X21) @ (sk_B @ X21)))
% 9.42/9.62          | ~ (l1_struct_0 @ X21)
% 9.42/9.62          | (v2_struct_0 @ X21))),
% 9.42/9.62      inference('cnf', [status(esa)], [d1_tex_1])).
% 9.42/9.62  thf('210', plain,
% 9.42/9.62      (((u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62         = (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['130', '137'])).
% 9.42/9.62  thf('211', plain,
% 9.42/9.62      (![X8 : $i]:
% 9.42/9.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 9.42/9.62          | ~ (l1_struct_0 @ X8)
% 9.42/9.62          | (v2_struct_0 @ X8))),
% 9.42/9.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 9.42/9.62  thf('212', plain,
% 9.42/9.62      ((~ (v1_xboole_0 @ 
% 9.42/9.62           (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62        | ~ (l1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('sup-', [status(thm)], ['210', '211'])).
% 9.42/9.62  thf('213', plain,
% 9.42/9.62      ((m1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)) @ sk_B_1)),
% 9.42/9.62      inference('clc', [status(thm)], ['105', '106'])).
% 9.42/9.62  thf('214', plain,
% 9.42/9.62      (![X5 : $i, X6 : $i]:
% 9.42/9.62         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 9.42/9.62      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 9.42/9.62  thf('215', plain,
% 9.42/9.62      ((~ (l1_pre_topc @ sk_B_1)
% 9.42/9.62        | (l1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('sup-', [status(thm)], ['213', '214'])).
% 9.42/9.62  thf('216', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.62      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.62  thf('217', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('demod', [status(thm)], ['215', '216'])).
% 9.42/9.62  thf('218', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 9.42/9.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 9.42/9.62  thf('219', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['217', '218'])).
% 9.42/9.62  thf('220', plain,
% 9.42/9.62      ((~ (v1_xboole_0 @ 
% 9.42/9.62           (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('demod', [status(thm)], ['212', '219'])).
% 9.42/9.62  thf('221', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['135', '136'])).
% 9.42/9.62  thf('222', plain,
% 9.42/9.62      (~ (v1_xboole_0 @ 
% 9.42/9.62          (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['220', '221'])).
% 9.42/9.62  thf('223', plain,
% 9.42/9.62      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 9.42/9.62        | (v2_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (l1_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (v7_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('sup-', [status(thm)], ['209', '222'])).
% 9.42/9.62  thf('224', plain, ((l1_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('sup-', [status(thm)], ['93', '94'])).
% 9.42/9.62  thf('225', plain, ((v7_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('226', plain,
% 9.42/9.62      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)) | (v2_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('demod', [status(thm)], ['223', '224', '225'])).
% 9.42/9.62  thf('227', plain, (~ (v2_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('228', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('clc', [status(thm)], ['226', '227'])).
% 9.42/9.62  thf('229', plain,
% 9.42/9.62      (~ (v2_struct_0 @ 
% 9.42/9.62          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['208', '228'])).
% 9.42/9.62  thf('230', plain,
% 9.42/9.62      (((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62         = (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['168', '229'])).
% 9.42/9.62  thf('231', plain,
% 9.42/9.62      (((u1_struct_0 @ sk_B_1)
% 9.42/9.62         = (u1_struct_0 @ 
% 9.42/9.62            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 9.42/9.62      inference('demod', [status(thm)], ['61', '62'])).
% 9.42/9.62  thf('232', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('233', plain,
% 9.42/9.62      (![X0 : $i, X1 : $i]:
% 9.42/9.62         (~ (m1_pre_topc @ X0 @ X1)
% 9.42/9.62          | (m1_subset_1 @ (sk_B @ X0) @ (u1_struct_0 @ X1))
% 9.42/9.62          | ~ (l1_pre_topc @ X1)
% 9.42/9.62          | (v2_struct_0 @ X1)
% 9.42/9.62          | ~ (v7_struct_0 @ X0)
% 9.42/9.62          | ~ (l1_struct_0 @ X0)
% 9.42/9.62          | (v2_struct_0 @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['90'])).
% 9.42/9.62  thf('234', plain,
% 9.42/9.62      (((v2_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (l1_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (v7_struct_0 @ sk_B_1)
% 9.42/9.62        | (v2_struct_0 @ sk_A)
% 9.42/9.62        | ~ (l1_pre_topc @ sk_A)
% 9.42/9.62        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['232', '233'])).
% 9.42/9.62  thf('235', plain, ((l1_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('sup-', [status(thm)], ['93', '94'])).
% 9.42/9.62  thf('236', plain, ((v7_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('237', plain, ((l1_pre_topc @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('238', plain,
% 9.42/9.62      (((v2_struct_0 @ sk_B_1)
% 9.42/9.62        | (v2_struct_0 @ sk_A)
% 9.42/9.62        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('demod', [status(thm)], ['234', '235', '236', '237'])).
% 9.42/9.62  thf('239', plain, (~ (v2_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('240', plain,
% 9.42/9.62      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 9.42/9.62        | (v2_struct_0 @ sk_A))),
% 9.42/9.62      inference('clc', [status(thm)], ['238', '239'])).
% 9.42/9.62  thf('241', plain, (~ (v2_struct_0 @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('242', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 9.42/9.62      inference('clc', [status(thm)], ['240', '241'])).
% 9.42/9.62  thf(redefinition_k6_domain_1, axiom,
% 9.42/9.62    (![A:$i,B:$i]:
% 9.42/9.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 9.42/9.62       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 9.42/9.62  thf('243', plain,
% 9.42/9.62      (![X14 : $i, X15 : $i]:
% 9.42/9.62         ((v1_xboole_0 @ X14)
% 9.42/9.62          | ~ (m1_subset_1 @ X15 @ X14)
% 9.42/9.62          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 9.42/9.62      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 9.42/9.62  thf('244', plain,
% 9.42/9.62      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 9.42/9.62          = (k1_tarski @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['242', '243'])).
% 9.42/9.62  thf('245', plain,
% 9.42/9.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 9.42/9.62         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 9.42/9.62          | ((u1_struct_0 @ X25) != (k6_domain_1 @ (u1_struct_0 @ X24) @ X23))
% 9.42/9.62          | ((X25) = (k1_tex_2 @ X24 @ X23))
% 9.42/9.62          | ~ (m1_pre_topc @ X25 @ X24)
% 9.42/9.62          | ~ (v1_pre_topc @ X25)
% 9.42/9.62          | (v2_struct_0 @ X25)
% 9.42/9.62          | ~ (l1_pre_topc @ X24)
% 9.42/9.62          | (v2_struct_0 @ X24))),
% 9.42/9.62      inference('cnf', [status(esa)], [d4_tex_2])).
% 9.42/9.62  thf('246', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (((u1_struct_0 @ X0) != (k1_tarski @ (sk_B @ sk_B_1)))
% 9.42/9.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 9.42/9.62          | (v2_struct_0 @ sk_A)
% 9.42/9.62          | ~ (l1_pre_topc @ sk_A)
% 9.42/9.62          | (v2_struct_0 @ X0)
% 9.42/9.62          | ~ (v1_pre_topc @ X0)
% 9.42/9.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 9.42/9.62          | ((X0) = (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62          | ~ (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['244', '245'])).
% 9.42/9.62  thf('247', plain, ((l1_pre_topc @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('248', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 9.42/9.62      inference('clc', [status(thm)], ['240', '241'])).
% 9.42/9.62  thf('249', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (((u1_struct_0 @ X0) != (k1_tarski @ (sk_B @ sk_B_1)))
% 9.42/9.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 9.42/9.62          | (v2_struct_0 @ sk_A)
% 9.42/9.62          | (v2_struct_0 @ X0)
% 9.42/9.62          | ~ (v1_pre_topc @ X0)
% 9.42/9.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 9.42/9.62          | ((X0) = (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('demod', [status(thm)], ['246', '247', '248'])).
% 9.42/9.62  thf('250', plain,
% 9.42/9.62      (![X21 : $i]:
% 9.42/9.62         (~ (v7_struct_0 @ X21)
% 9.42/9.62          | ((u1_struct_0 @ X21)
% 9.42/9.62              = (k6_domain_1 @ (u1_struct_0 @ X21) @ (sk_B @ X21)))
% 9.42/9.62          | ~ (l1_struct_0 @ X21)
% 9.42/9.62          | (v2_struct_0 @ X21))),
% 9.42/9.62      inference('cnf', [status(esa)], [d1_tex_1])).
% 9.42/9.62  thf('251', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('clc', [status(thm)], ['99', '100'])).
% 9.42/9.62  thf('252', plain,
% 9.42/9.62      (![X14 : $i, X15 : $i]:
% 9.42/9.62         ((v1_xboole_0 @ X14)
% 9.42/9.62          | ~ (m1_subset_1 @ X15 @ X14)
% 9.42/9.62          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 9.42/9.62      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 9.42/9.62  thf('253', plain,
% 9.42/9.62      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1))
% 9.42/9.62          = (k1_tarski @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['251', '252'])).
% 9.42/9.62  thf('254', plain,
% 9.42/9.62      ((((u1_struct_0 @ sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (l1_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (v7_struct_0 @ sk_B_1)
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 9.42/9.62      inference('sup+', [status(thm)], ['250', '253'])).
% 9.42/9.62  thf('255', plain, ((l1_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('sup-', [status(thm)], ['93', '94'])).
% 9.42/9.62  thf('256', plain, ((v7_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('257', plain,
% 9.42/9.62      ((((u1_struct_0 @ sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_B_1)
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 9.42/9.62      inference('demod', [status(thm)], ['254', '255', '256'])).
% 9.42/9.62  thf('258', plain, (~ (v2_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('259', plain,
% 9.42/9.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 9.42/9.62        | ((u1_struct_0 @ sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('clc', [status(thm)], ['257', '258'])).
% 9.42/9.62  thf('260', plain,
% 9.42/9.62      (![X8 : $i]:
% 9.42/9.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 9.42/9.62          | ~ (l1_struct_0 @ X8)
% 9.42/9.62          | (v2_struct_0 @ X8))),
% 9.42/9.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 9.42/9.62  thf('261', plain,
% 9.42/9.62      ((((u1_struct_0 @ sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (l1_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('sup-', [status(thm)], ['259', '260'])).
% 9.42/9.62  thf('262', plain, ((l1_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('sup-', [status(thm)], ['93', '94'])).
% 9.42/9.62  thf('263', plain,
% 9.42/9.62      ((((u1_struct_0 @ sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('demod', [status(thm)], ['261', '262'])).
% 9.42/9.62  thf('264', plain, (~ (v2_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('265', plain, (((u1_struct_0 @ sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['263', '264'])).
% 9.42/9.62  thf('266', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (((u1_struct_0 @ X0) != (u1_struct_0 @ sk_B_1))
% 9.42/9.62          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 9.42/9.62          | (v2_struct_0 @ sk_A)
% 9.42/9.62          | (v2_struct_0 @ X0)
% 9.42/9.62          | ~ (v1_pre_topc @ X0)
% 9.42/9.62          | ~ (m1_pre_topc @ X0 @ sk_A)
% 9.42/9.62          | ((X0) = (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('demod', [status(thm)], ['249', '265'])).
% 9.42/9.62  thf('267', plain,
% 9.42/9.62      ((((u1_struct_0 @ sk_B_1) != (u1_struct_0 @ sk_B_1))
% 9.42/9.62        | ((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62            = (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62        | ~ (m1_pre_topc @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)) @ 
% 9.42/9.62             sk_A)
% 9.42/9.62        | ~ (v1_pre_topc @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_A)
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['231', '266'])).
% 9.42/9.62  thf('268', plain,
% 9.42/9.62      ((m1_pre_topc @ 
% 9.42/9.62        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)) @ sk_A)),
% 9.42/9.62      inference('demod', [status(thm)], ['26', '27'])).
% 9.42/9.62  thf('269', plain,
% 9.42/9.62      ((v1_pre_topc @ 
% 9.42/9.62        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 9.42/9.62      inference('demod', [status(thm)], ['162', '163'])).
% 9.42/9.62  thf('270', plain,
% 9.42/9.62      ((((u1_struct_0 @ sk_B_1) != (u1_struct_0 @ sk_B_1))
% 9.42/9.62        | ((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62            = (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_A)
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('demod', [status(thm)], ['267', '268', '269'])).
% 9.42/9.62  thf('271', plain,
% 9.42/9.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 9.42/9.62        | (v2_struct_0 @ sk_A)
% 9.42/9.62        | (v2_struct_0 @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 9.42/9.62        | ((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62            = (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('simplify', [status(thm)], ['270'])).
% 9.42/9.62  thf('272', plain,
% 9.42/9.62      (~ (v2_struct_0 @ 
% 9.42/9.62          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['208', '228'])).
% 9.42/9.62  thf('273', plain,
% 9.42/9.62      ((((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62          = (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_A)
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['271', '272'])).
% 9.42/9.62  thf('274', plain, (~ (v2_struct_0 @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('275', plain,
% 9.42/9.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 9.42/9.62        | ((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62            = (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('clc', [status(thm)], ['273', '274'])).
% 9.42/9.62  thf('276', plain,
% 9.42/9.62      ((((k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))
% 9.42/9.62          = (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('sup+', [status(thm)], ['230', '275'])).
% 9.42/9.62  thf('277', plain,
% 9.42/9.62      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 9.42/9.62          = (k1_tarski @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['242', '243'])).
% 9.42/9.62  thf('278', plain, (((u1_struct_0 @ sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['263', '264'])).
% 9.42/9.62  thf('279', plain,
% 9.42/9.62      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 9.42/9.62          = (u1_struct_0 @ sk_B_1))
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('demod', [status(thm)], ['277', '278'])).
% 9.42/9.62  thf('280', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 9.42/9.62      inference('clc', [status(thm)], ['240', '241'])).
% 9.42/9.62  thf('281', plain,
% 9.42/9.62      (![X26 : $i, X27 : $i]:
% 9.42/9.62         (~ (l1_pre_topc @ X26)
% 9.42/9.62          | (v2_struct_0 @ X26)
% 9.42/9.62          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 9.42/9.62          | (v1_pre_topc @ (k1_tex_2 @ X26 @ X27)))),
% 9.42/9.62      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 9.42/9.62  thf('282', plain,
% 9.42/9.62      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_A)
% 9.42/9.62        | ~ (l1_pre_topc @ sk_A))),
% 9.42/9.62      inference('sup-', [status(thm)], ['280', '281'])).
% 9.42/9.62  thf('283', plain, ((l1_pre_topc @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('284', plain,
% 9.42/9.62      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_A))),
% 9.42/9.62      inference('demod', [status(thm)], ['282', '283'])).
% 9.42/9.62  thf('285', plain, (~ (v2_struct_0 @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('286', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['284', '285'])).
% 9.42/9.62  thf('287', plain,
% 9.42/9.62      (![X23 : $i, X24 : $i]:
% 9.42/9.62         ((v2_struct_0 @ X24)
% 9.42/9.62          | ~ (l1_pre_topc @ X24)
% 9.42/9.62          | (v2_struct_0 @ (k1_tex_2 @ X24 @ X23))
% 9.42/9.62          | ~ (v1_pre_topc @ (k1_tex_2 @ X24 @ X23))
% 9.42/9.62          | ~ (m1_pre_topc @ (k1_tex_2 @ X24 @ X23) @ X24)
% 9.42/9.62          | ((u1_struct_0 @ (k1_tex_2 @ X24 @ X23))
% 9.42/9.62              = (k6_domain_1 @ (u1_struct_0 @ X24) @ X23))
% 9.42/9.62          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24)))),
% 9.42/9.62      inference('simplify', [status(thm)], ['119'])).
% 9.42/9.62  thf('288', plain,
% 9.42/9.62      ((~ (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 9.42/9.62        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)))
% 9.42/9.62        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)
% 9.42/9.62        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62        | ~ (l1_pre_topc @ sk_A)
% 9.42/9.62        | (v2_struct_0 @ sk_A))),
% 9.42/9.62      inference('sup-', [status(thm)], ['286', '287'])).
% 9.42/9.62  thf('289', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 9.42/9.62      inference('clc', [status(thm)], ['240', '241'])).
% 9.42/9.62  thf('290', plain, ((l1_pre_topc @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('291', plain,
% 9.42/9.62      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)))
% 9.42/9.62        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)
% 9.42/9.62        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_A))),
% 9.42/9.62      inference('demod', [status(thm)], ['288', '289', '290'])).
% 9.42/9.62  thf('292', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 9.42/9.62      inference('clc', [status(thm)], ['240', '241'])).
% 9.42/9.62  thf('293', plain,
% 9.42/9.62      (![X26 : $i, X27 : $i]:
% 9.42/9.62         (~ (l1_pre_topc @ X26)
% 9.42/9.62          | (v2_struct_0 @ X26)
% 9.42/9.62          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 9.42/9.62          | (m1_pre_topc @ (k1_tex_2 @ X26 @ X27) @ X26))),
% 9.42/9.62      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 9.42/9.62  thf('294', plain,
% 9.42/9.62      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)
% 9.42/9.62        | (v2_struct_0 @ sk_A)
% 9.42/9.62        | ~ (l1_pre_topc @ sk_A))),
% 9.42/9.62      inference('sup-', [status(thm)], ['292', '293'])).
% 9.42/9.62  thf('295', plain, ((l1_pre_topc @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('296', plain,
% 9.42/9.62      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)
% 9.42/9.62        | (v2_struct_0 @ sk_A))),
% 9.42/9.62      inference('demod', [status(thm)], ['294', '295'])).
% 9.42/9.62  thf('297', plain, (~ (v2_struct_0 @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('298', plain,
% 9.42/9.62      ((m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)),
% 9.42/9.62      inference('clc', [status(thm)], ['296', '297'])).
% 9.42/9.62  thf('299', plain,
% 9.42/9.62      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_A))),
% 9.42/9.62      inference('demod', [status(thm)], ['291', '298'])).
% 9.42/9.62  thf('300', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 9.42/9.62      inference('clc', [status(thm)], ['240', '241'])).
% 9.42/9.62  thf('301', plain,
% 9.42/9.62      (![X26 : $i, X27 : $i]:
% 9.42/9.62         (~ (l1_pre_topc @ X26)
% 9.42/9.62          | (v2_struct_0 @ X26)
% 9.42/9.62          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 9.42/9.62          | ~ (v2_struct_0 @ (k1_tex_2 @ X26 @ X27)))),
% 9.42/9.62      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 9.42/9.62  thf('302', plain,
% 9.42/9.62      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_A)
% 9.42/9.62        | ~ (l1_pre_topc @ sk_A))),
% 9.42/9.62      inference('sup-', [status(thm)], ['300', '301'])).
% 9.42/9.62  thf('303', plain, ((l1_pre_topc @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('304', plain,
% 9.42/9.62      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ sk_A))),
% 9.42/9.62      inference('demod', [status(thm)], ['302', '303'])).
% 9.42/9.62  thf('305', plain, (~ (v2_struct_0 @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('306', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['304', '305'])).
% 9.42/9.62  thf('307', plain,
% 9.42/9.62      (((v2_struct_0 @ sk_A)
% 9.42/9.62        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('clc', [status(thm)], ['299', '306'])).
% 9.42/9.62  thf('308', plain, (~ (v2_struct_0 @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('309', plain,
% 9.42/9.62      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 9.42/9.62         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['307', '308'])).
% 9.42/9.62  thf('310', plain,
% 9.42/9.62      (![X28 : $i]:
% 9.42/9.62         (((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62            != (g1_pre_topc @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ X28)) @ 
% 9.42/9.62                (u1_pre_topc @ (k1_tex_2 @ sk_A @ X28))))
% 9.42/9.62          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('311', plain,
% 9.42/9.62      ((((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62          != (g1_pre_topc @ 
% 9.42/9.62              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 9.42/9.62              (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))))
% 9.42/9.62        | ~ (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['309', '310'])).
% 9.42/9.62  thf('312', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 9.42/9.62      inference('clc', [status(thm)], ['240', '241'])).
% 9.42/9.62  thf('313', plain,
% 9.42/9.62      (((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62         != (g1_pre_topc @ 
% 9.42/9.62             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 9.42/9.62             (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))))),
% 9.42/9.62      inference('demod', [status(thm)], ['311', '312'])).
% 9.42/9.62  thf('314', plain,
% 9.42/9.62      ((((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62          != (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62              (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))))
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['279', '313'])).
% 9.42/9.62  thf('315', plain,
% 9.42/9.62      (((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 9.42/9.62         = (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['168', '229'])).
% 9.42/9.62  thf('316', plain,
% 9.42/9.62      ((((k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))
% 9.42/9.62          != (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62              (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))))
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('demod', [status(thm)], ['314', '315'])).
% 9.42/9.62  thf('317', plain,
% 9.42/9.62      ((((k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))
% 9.42/9.62          != (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62              (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 9.42/9.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 9.42/9.62      inference('sup-', [status(thm)], ['276', '316'])).
% 9.42/9.62  thf('318', plain,
% 9.42/9.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 9.42/9.62        | ((k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))
% 9.42/9.62            != (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62                (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))))),
% 9.42/9.62      inference('simplify', [status(thm)], ['317'])).
% 9.42/9.62  thf('319', plain,
% 9.42/9.62      (((u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62         = (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['130', '137'])).
% 9.42/9.62  thf('320', plain,
% 9.42/9.62      (((u1_struct_0 @ sk_B_1)
% 9.42/9.62         = (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['146', '147'])).
% 9.42/9.62  thf('321', plain,
% 9.42/9.62      (((u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62         = (u1_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('demod', [status(thm)], ['319', '320'])).
% 9.42/9.62  thf('322', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (((u1_struct_0 @ X0)
% 9.42/9.62            = (u1_struct_0 @ 
% 9.42/9.62               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['22'])).
% 9.42/9.62  thf('323', plain,
% 9.42/9.62      ((((u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62          = (u1_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62              (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))))
% 9.42/9.62        | ~ (l1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('sup+', [status(thm)], ['321', '322'])).
% 9.42/9.62  thf('324', plain,
% 9.42/9.62      (((u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62         = (u1_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('demod', [status(thm)], ['319', '320'])).
% 9.42/9.62  thf('325', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('demod', [status(thm)], ['215', '216'])).
% 9.42/9.62  thf('326', plain,
% 9.42/9.62      (((u1_struct_0 @ sk_B_1)
% 9.42/9.62         = (u1_struct_0 @ 
% 9.42/9.62            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62             (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))))),
% 9.42/9.62      inference('demod', [status(thm)], ['323', '324', '325'])).
% 9.42/9.62  thf('327', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (((u1_struct_0 @ X0) != (u1_struct_0 @ sk_B_1))
% 9.42/9.62          | (v2_struct_0 @ sk_B_1)
% 9.42/9.62          | (v2_struct_0 @ X0)
% 9.42/9.62          | ~ (v1_pre_topc @ X0)
% 9.42/9.62          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 9.42/9.62          | ((X0) = (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('demod', [status(thm)], ['150', '151', '152'])).
% 9.42/9.62  thf('328', plain,
% 9.42/9.62      ((((u1_struct_0 @ sk_B_1) != (u1_struct_0 @ sk_B_1))
% 9.42/9.62        | ((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62            (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))
% 9.42/9.62            = (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62        | ~ (m1_pre_topc @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62              (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))) @ 
% 9.42/9.62             sk_B_1)
% 9.42/9.62        | ~ (v1_pre_topc @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62              (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 9.42/9.62        | (v2_struct_0 @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62            (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 9.42/9.62        | (v2_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('sup-', [status(thm)], ['326', '327'])).
% 9.42/9.62  thf('329', plain,
% 9.42/9.62      (((u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62         = (u1_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('demod', [status(thm)], ['319', '320'])).
% 9.42/9.62  thf('330', plain,
% 9.42/9.62      (![X21 : $i]:
% 9.42/9.62         (~ (v7_struct_0 @ X21)
% 9.42/9.62          | (m1_subset_1 @ (sk_B @ X21) @ (u1_struct_0 @ X21))
% 9.42/9.62          | ~ (l1_struct_0 @ X21)
% 9.42/9.62          | (v2_struct_0 @ X21))),
% 9.42/9.62      inference('cnf', [status(esa)], [d1_tex_1])).
% 9.42/9.62  thf('331', plain,
% 9.42/9.62      (![X26 : $i, X27 : $i]:
% 9.42/9.62         (~ (l1_pre_topc @ X26)
% 9.42/9.62          | (v2_struct_0 @ X26)
% 9.42/9.62          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 9.42/9.62          | (m1_pre_topc @ (k1_tex_2 @ X26 @ X27) @ X26))),
% 9.42/9.62      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 9.42/9.62  thf('332', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         ((v2_struct_0 @ X0)
% 9.42/9.62          | ~ (l1_struct_0 @ X0)
% 9.42/9.62          | ~ (v7_struct_0 @ X0)
% 9.42/9.62          | (m1_pre_topc @ (k1_tex_2 @ X0 @ (sk_B @ X0)) @ X0)
% 9.42/9.62          | (v2_struct_0 @ X0)
% 9.42/9.62          | ~ (l1_pre_topc @ X0))),
% 9.42/9.62      inference('sup-', [status(thm)], ['330', '331'])).
% 9.42/9.62  thf('333', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (l1_pre_topc @ X0)
% 9.42/9.62          | (m1_pre_topc @ (k1_tex_2 @ X0 @ (sk_B @ X0)) @ X0)
% 9.42/9.62          | ~ (v7_struct_0 @ X0)
% 9.42/9.62          | ~ (l1_struct_0 @ X0)
% 9.42/9.62          | (v2_struct_0 @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['332'])).
% 9.42/9.62  thf('334', plain,
% 9.42/9.62      (![X16 : $i, X17 : $i]:
% 9.42/9.62         (~ (m1_pre_topc @ X16 @ X17)
% 9.42/9.62          | (m1_pre_topc @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)) @ X17)
% 9.42/9.62          | ~ (l1_pre_topc @ X17))),
% 9.42/9.62      inference('cnf', [status(esa)], [t11_tmap_1])).
% 9.42/9.62  thf('335', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         ((v2_struct_0 @ X0)
% 9.42/9.62          | ~ (l1_struct_0 @ X0)
% 9.42/9.62          | ~ (v7_struct_0 @ X0)
% 9.42/9.62          | ~ (l1_pre_topc @ X0)
% 9.42/9.62          | ~ (l1_pre_topc @ X0)
% 9.42/9.62          | (m1_pre_topc @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ (k1_tex_2 @ X0 @ (sk_B @ X0))) @ 
% 9.42/9.62              (u1_pre_topc @ (k1_tex_2 @ X0 @ (sk_B @ X0)))) @ 
% 9.42/9.62             X0))),
% 9.42/9.62      inference('sup-', [status(thm)], ['333', '334'])).
% 9.42/9.62  thf('336', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         ((m1_pre_topc @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ (k1_tex_2 @ X0 @ (sk_B @ X0))) @ 
% 9.42/9.62            (u1_pre_topc @ (k1_tex_2 @ X0 @ (sk_B @ X0)))) @ 
% 9.42/9.62           X0)
% 9.42/9.62          | ~ (l1_pre_topc @ X0)
% 9.42/9.62          | ~ (v7_struct_0 @ X0)
% 9.42/9.62          | ~ (l1_struct_0 @ X0)
% 9.42/9.62          | (v2_struct_0 @ X0))),
% 9.42/9.62      inference('simplify', [status(thm)], ['335'])).
% 9.42/9.62  thf('337', plain,
% 9.42/9.62      (((m1_pre_topc @ 
% 9.42/9.62         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62          (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))) @ 
% 9.42/9.62         sk_B_1)
% 9.42/9.62        | (v2_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (l1_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (v7_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (l1_pre_topc @ sk_B_1))),
% 9.42/9.62      inference('sup+', [status(thm)], ['329', '336'])).
% 9.42/9.62  thf('338', plain, ((l1_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('sup-', [status(thm)], ['93', '94'])).
% 9.42/9.62  thf('339', plain, ((v7_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('340', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.62      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.62  thf('341', plain,
% 9.42/9.62      (((m1_pre_topc @ 
% 9.42/9.62         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62          (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))) @ 
% 9.42/9.62         sk_B_1)
% 9.42/9.62        | (v2_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('demod', [status(thm)], ['337', '338', '339', '340'])).
% 9.42/9.62  thf('342', plain, (~ (v2_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('343', plain,
% 9.42/9.62      ((m1_pre_topc @ 
% 9.42/9.62        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62         (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))) @ 
% 9.42/9.62        sk_B_1)),
% 9.42/9.62      inference('clc', [status(thm)], ['341', '342'])).
% 9.42/9.62  thf('344', plain,
% 9.42/9.62      (![X21 : $i]:
% 9.42/9.62         (~ (v7_struct_0 @ X21)
% 9.42/9.62          | ((u1_struct_0 @ X21)
% 9.42/9.62              = (k6_domain_1 @ (u1_struct_0 @ X21) @ (sk_B @ X21)))
% 9.42/9.62          | ~ (l1_struct_0 @ X21)
% 9.42/9.62          | (v2_struct_0 @ X21))),
% 9.42/9.62      inference('cnf', [status(esa)], [d1_tex_1])).
% 9.42/9.62  thf('345', plain,
% 9.42/9.62      ((m1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)) @ sk_B_1)),
% 9.42/9.62      inference('clc', [status(thm)], ['105', '106'])).
% 9.42/9.62  thf('346', plain,
% 9.42/9.62      (![X16 : $i, X17 : $i]:
% 9.42/9.62         (~ (m1_pre_topc @ X16 @ X17)
% 9.42/9.62          | (v1_pre_topc @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 9.42/9.62          | ~ (l1_pre_topc @ X17))),
% 9.42/9.62      inference('cnf', [status(esa)], [t11_tmap_1])).
% 9.42/9.62  thf('347', plain,
% 9.42/9.62      ((~ (l1_pre_topc @ sk_B_1)
% 9.42/9.62        | (v1_pre_topc @ 
% 9.42/9.62           (g1_pre_topc @ 
% 9.42/9.62            (u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))) @ 
% 9.42/9.62            (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))))),
% 9.42/9.62      inference('sup-', [status(thm)], ['345', '346'])).
% 9.42/9.62  thf('348', plain, ((l1_pre_topc @ sk_B_1)),
% 9.42/9.62      inference('demod', [status(thm)], ['43', '44'])).
% 9.42/9.62  thf('349', plain,
% 9.42/9.62      ((v1_pre_topc @ 
% 9.42/9.62        (g1_pre_topc @ (u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))) @ 
% 9.42/9.62         (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))),
% 9.42/9.62      inference('demod', [status(thm)], ['347', '348'])).
% 9.42/9.62  thf('350', plain,
% 9.42/9.62      (((u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62         = (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['130', '137'])).
% 9.42/9.62  thf('351', plain,
% 9.42/9.62      ((v1_pre_topc @ 
% 9.42/9.62        (g1_pre_topc @ 
% 9.42/9.62         (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ (sk_B @ sk_B_1)) @ 
% 9.42/9.62         (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))),
% 9.42/9.62      inference('demod', [status(thm)], ['349', '350'])).
% 9.42/9.62  thf('352', plain,
% 9.42/9.62      (((v1_pre_topc @ 
% 9.42/9.62         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62          (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 9.42/9.62        | (v2_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (l1_struct_0 @ sk_B_1)
% 9.42/9.62        | ~ (v7_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('sup+', [status(thm)], ['344', '351'])).
% 9.42/9.62  thf('353', plain, ((l1_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('sup-', [status(thm)], ['93', '94'])).
% 9.42/9.62  thf('354', plain, ((v7_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('355', plain,
% 9.42/9.62      (((v1_pre_topc @ 
% 9.42/9.62         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62          (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 9.42/9.62        | (v2_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('demod', [status(thm)], ['352', '353', '354'])).
% 9.42/9.62  thf('356', plain, (~ (v2_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('357', plain,
% 9.42/9.62      ((v1_pre_topc @ 
% 9.42/9.62        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62         (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))),
% 9.42/9.62      inference('clc', [status(thm)], ['355', '356'])).
% 9.42/9.62  thf('358', plain,
% 9.42/9.62      ((((u1_struct_0 @ sk_B_1) != (u1_struct_0 @ sk_B_1))
% 9.42/9.62        | ((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62            (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))
% 9.42/9.62            = (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62            (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 9.42/9.62        | (v2_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('demod', [status(thm)], ['328', '343', '357'])).
% 9.42/9.62  thf('359', plain,
% 9.42/9.62      (((v2_struct_0 @ sk_B_1)
% 9.42/9.62        | (v2_struct_0 @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62            (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 9.42/9.62        | ((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62            (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))
% 9.42/9.62            = (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('simplify', [status(thm)], ['358'])).
% 9.42/9.62  thf('360', plain, (~ (v2_struct_0 @ sk_B_1)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('361', plain,
% 9.42/9.62      ((((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62          (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))
% 9.42/9.62          = (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62        | (v2_struct_0 @ 
% 9.42/9.62           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62            (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))))),
% 9.42/9.62      inference('clc', [status(thm)], ['359', '360'])).
% 9.42/9.62  thf('362', plain,
% 9.42/9.62      (((u1_struct_0 @ sk_B_1)
% 9.42/9.62         = (u1_struct_0 @ 
% 9.42/9.62            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62             (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))))),
% 9.42/9.62      inference('demod', [status(thm)], ['323', '324', '325'])).
% 9.42/9.62  thf('363', plain,
% 9.42/9.62      (![X7 : $i]:
% 9.42/9.62         ((v1_xboole_0 @ (u1_struct_0 @ X7))
% 9.42/9.62          | ~ (l1_struct_0 @ X7)
% 9.42/9.62          | ~ (v2_struct_0 @ X7))),
% 9.42/9.62      inference('cnf', [status(esa)], [fc1_struct_0])).
% 9.42/9.62  thf('364', plain,
% 9.42/9.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 9.42/9.62        | ~ (v2_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62              (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 9.42/9.62        | ~ (l1_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62              (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))))),
% 9.42/9.62      inference('sup+', [status(thm)], ['362', '363'])).
% 9.42/9.62  thf('365', plain,
% 9.42/9.62      (((u1_struct_0 @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 9.42/9.62         = (u1_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('demod', [status(thm)], ['319', '320'])).
% 9.42/9.62  thf('366', plain,
% 9.42/9.62      (![X0 : $i]:
% 9.42/9.62         (~ (l1_pre_topc @ X0)
% 9.42/9.62          | (l1_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 9.42/9.62      inference('sup-', [status(thm)], ['172', '173'])).
% 9.42/9.62  thf('367', plain,
% 9.42/9.62      (((l1_struct_0 @ 
% 9.42/9.62         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62          (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 9.42/9.62        | ~ (l1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('sup+', [status(thm)], ['365', '366'])).
% 9.42/9.62  thf('368', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('demod', [status(thm)], ['215', '216'])).
% 9.42/9.62  thf('369', plain,
% 9.42/9.62      ((l1_struct_0 @ 
% 9.42/9.62        (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62         (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))),
% 9.42/9.62      inference('demod', [status(thm)], ['367', '368'])).
% 9.42/9.62  thf('370', plain,
% 9.42/9.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 9.42/9.62        | ~ (v2_struct_0 @ 
% 9.42/9.62             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62              (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))))),
% 9.42/9.62      inference('demod', [status(thm)], ['364', '369'])).
% 9.42/9.62  thf('371', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 9.42/9.62      inference('clc', [status(thm)], ['226', '227'])).
% 9.42/9.62  thf('372', plain,
% 9.42/9.62      (~ (v2_struct_0 @ 
% 9.42/9.62          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62           (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))))),
% 9.42/9.62      inference('clc', [status(thm)], ['370', '371'])).
% 9.42/9.62  thf('373', plain,
% 9.42/9.62      (((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ 
% 9.42/9.62         (u1_pre_topc @ (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))
% 9.42/9.62         = (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 9.42/9.62      inference('clc', [status(thm)], ['361', '372'])).
% 9.42/9.62  thf('374', plain,
% 9.42/9.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 9.42/9.62        | ((k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))
% 9.42/9.62            != (k1_tex_2 @ sk_B_1 @ (sk_B @ sk_B_1))))),
% 9.42/9.62      inference('demod', [status(thm)], ['318', '373'])).
% 9.42/9.62  thf('375', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 9.42/9.62      inference('simplify', [status(thm)], ['374'])).
% 9.42/9.62  thf('376', plain,
% 9.42/9.62      (![X8 : $i]:
% 9.42/9.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 9.42/9.62          | ~ (l1_struct_0 @ X8)
% 9.42/9.62          | (v2_struct_0 @ X8))),
% 9.42/9.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 9.42/9.62  thf('377', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 9.42/9.62      inference('sup-', [status(thm)], ['375', '376'])).
% 9.42/9.62  thf('378', plain, ((l1_pre_topc @ sk_A)),
% 9.42/9.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.42/9.62  thf('379', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 9.42/9.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 9.42/9.62  thf('380', plain, ((l1_struct_0 @ sk_A)),
% 9.42/9.62      inference('sup-', [status(thm)], ['378', '379'])).
% 9.42/9.62  thf('381', plain, ((v2_struct_0 @ sk_A)),
% 9.42/9.62      inference('demod', [status(thm)], ['377', '380'])).
% 9.42/9.62  thf('382', plain, ($false), inference('demod', [status(thm)], ['0', '381'])).
% 9.42/9.62  
% 9.42/9.62  % SZS output end Refutation
% 9.42/9.62  
% 9.42/9.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
