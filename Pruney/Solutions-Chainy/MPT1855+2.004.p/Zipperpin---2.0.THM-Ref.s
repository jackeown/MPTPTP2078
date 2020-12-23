%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ycfqtJdwTr

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:10 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 829 expanded)
%              Number of leaves         :   27 ( 245 expanded)
%              Depth                    :   33
%              Number of atoms          : 1220 (13187 expanded)
%              Number of equality atoms :   46 ( 365 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tex_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( ( v7_struct_0 @ A )
      <=> ? [B: $i] :
            ( ( ( u1_struct_0 @ A )
              = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
            & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ~ ( v7_struct_0 @ X12 )
      | ( ( u1_struct_0 @ X12 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X12 ) @ ( sk_B @ X12 ) ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('2',plain,(
    ! [X12: $i] :
      ( ~ ( v7_struct_0 @ X12 )
      | ( m1_subset_1 @ ( sk_B @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( ( k6_domain_1 @ X7 @ X8 )
        = ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X12: $i] :
      ( ~ ( v7_struct_0 @ X12 )
      | ( m1_subset_1 @ ( sk_B @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
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

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( m1_pre_topc @ X4 @ X5 )
      | ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( v7_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('19',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','19','20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X17 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('28',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( ( k6_domain_1 @ X7 @ X8 )
        = ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('35',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('38',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

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

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( X16
       != ( k1_tex_2 @ X15 @ X14 ) )
      | ( ( u1_struct_0 @ X16 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X15 ) @ X14 ) )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( v1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X15 @ X14 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X15 @ X14 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X15 @ X14 ) @ X15 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X15 @ X14 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X15 ) @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['30','31'])).

thf('50',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('53',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['50','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf(t5_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( ( u1_struct_0 @ B )
                  = ( u1_struct_0 @ C ) )
               => ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( ( u1_struct_0 @ X9 )
       != ( u1_struct_0 @ X11 ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t5_tsep_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ X0 )
       != ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ X0 )
       != ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ~ ( v7_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('71',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
      = ( g1_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(eq_res,[status(thm)],['72'])).

thf('74',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
      = ( g1_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('77',plain,(
    ! [X19: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ X19 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ X19 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
     != ( g1_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('80',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
 != ( g1_pre_topc @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['75','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('84',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('88',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('95',plain,(
    v2_struct_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ycfqtJdwTr
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:30:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.83/1.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.07  % Solved by: fo/fo7.sh
% 0.83/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.07  % done 725 iterations in 0.613s
% 0.83/1.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.07  % SZS output start Refutation
% 0.83/1.07  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.83/1.07  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.83/1.07  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.83/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.07  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.83/1.07  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.83/1.07  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.83/1.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.83/1.07  thf(sk_B_type, type, sk_B: $i > $i).
% 0.83/1.07  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.83/1.07  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.83/1.07  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.83/1.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.83/1.07  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.83/1.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.07  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.83/1.07  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.83/1.07  thf(t23_tex_2, conjecture,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.07       ( ![B:$i]:
% 0.83/1.07         ( ( ( ~( v2_struct_0 @ B ) ) & ( v7_struct_0 @ B ) & 
% 0.83/1.07             ( m1_pre_topc @ B @ A ) ) =>
% 0.83/1.07           ( ?[C:$i]:
% 0.83/1.07             ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.83/1.07                 ( g1_pre_topc @
% 0.83/1.07                   ( u1_struct_0 @ ( k1_tex_2 @ A @ C ) ) @ 
% 0.83/1.07                   ( u1_pre_topc @ ( k1_tex_2 @ A @ C ) ) ) ) & 
% 0.83/1.07               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.83/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.07    (~( ![A:$i]:
% 0.83/1.07        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.07          ( ![B:$i]:
% 0.83/1.07            ( ( ( ~( v2_struct_0 @ B ) ) & ( v7_struct_0 @ B ) & 
% 0.83/1.07                ( m1_pre_topc @ B @ A ) ) =>
% 0.83/1.07              ( ?[C:$i]:
% 0.83/1.07                ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.83/1.07                    ( g1_pre_topc @
% 0.83/1.07                      ( u1_struct_0 @ ( k1_tex_2 @ A @ C ) ) @ 
% 0.83/1.07                      ( u1_pre_topc @ ( k1_tex_2 @ A @ C ) ) ) ) & 
% 0.83/1.07                  ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.83/1.07    inference('cnf.neg', [status(esa)], [t23_tex_2])).
% 0.83/1.07  thf('0', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf(d1_tex_1, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.83/1.07       ( ( v7_struct_0 @ A ) <=>
% 0.83/1.07         ( ?[B:$i]:
% 0.83/1.07           ( ( ( u1_struct_0 @ A ) = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) & 
% 0.83/1.07             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.83/1.07  thf('1', plain,
% 0.83/1.07      (![X12 : $i]:
% 0.83/1.07         (~ (v7_struct_0 @ X12)
% 0.83/1.07          | ((u1_struct_0 @ X12)
% 0.83/1.07              = (k6_domain_1 @ (u1_struct_0 @ X12) @ (sk_B @ X12)))
% 0.83/1.07          | ~ (l1_struct_0 @ X12)
% 0.83/1.07          | (v2_struct_0 @ X12))),
% 0.83/1.07      inference('cnf', [status(esa)], [d1_tex_1])).
% 0.83/1.07  thf('2', plain,
% 0.83/1.07      (![X12 : $i]:
% 0.83/1.07         (~ (v7_struct_0 @ X12)
% 0.83/1.07          | (m1_subset_1 @ (sk_B @ X12) @ (u1_struct_0 @ X12))
% 0.83/1.07          | ~ (l1_struct_0 @ X12)
% 0.83/1.07          | (v2_struct_0 @ X12))),
% 0.83/1.07      inference('cnf', [status(esa)], [d1_tex_1])).
% 0.83/1.07  thf(redefinition_k6_domain_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.83/1.07       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.83/1.07  thf('3', plain,
% 0.83/1.07      (![X7 : $i, X8 : $i]:
% 0.83/1.07         ((v1_xboole_0 @ X7)
% 0.83/1.07          | ~ (m1_subset_1 @ X8 @ X7)
% 0.83/1.07          | ((k6_domain_1 @ X7 @ X8) = (k1_tarski @ X8)))),
% 0.83/1.07      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.83/1.07  thf('4', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((v2_struct_0 @ X0)
% 0.83/1.07          | ~ (l1_struct_0 @ X0)
% 0.83/1.07          | ~ (v7_struct_0 @ X0)
% 0.83/1.07          | ((k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ X0))
% 0.83/1.07              = (k1_tarski @ (sk_B @ X0)))
% 0.83/1.07          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['2', '3'])).
% 0.83/1.07  thf('5', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (((u1_struct_0 @ X0) = (k1_tarski @ (sk_B @ X0)))
% 0.83/1.07          | (v2_struct_0 @ X0)
% 0.83/1.07          | ~ (l1_struct_0 @ X0)
% 0.83/1.07          | ~ (v7_struct_0 @ X0)
% 0.83/1.07          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.83/1.07          | ~ (v7_struct_0 @ X0)
% 0.83/1.07          | ~ (l1_struct_0 @ X0)
% 0.83/1.07          | (v2_struct_0 @ X0))),
% 0.83/1.07      inference('sup+', [status(thm)], ['1', '4'])).
% 0.83/1.07  thf('6', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.83/1.07          | ~ (v7_struct_0 @ X0)
% 0.83/1.07          | ~ (l1_struct_0 @ X0)
% 0.83/1.07          | (v2_struct_0 @ X0)
% 0.83/1.07          | ((u1_struct_0 @ X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.83/1.07      inference('simplify', [status(thm)], ['5'])).
% 0.83/1.07  thf('7', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('8', plain,
% 0.83/1.07      (![X12 : $i]:
% 0.83/1.07         (~ (v7_struct_0 @ X12)
% 0.83/1.07          | (m1_subset_1 @ (sk_B @ X12) @ (u1_struct_0 @ X12))
% 0.83/1.07          | ~ (l1_struct_0 @ X12)
% 0.83/1.07          | (v2_struct_0 @ X12))),
% 0.83/1.07      inference('cnf', [status(esa)], [d1_tex_1])).
% 0.83/1.07  thf(t55_pre_topc, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.07       ( ![B:$i]:
% 0.83/1.07         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.83/1.07           ( ![C:$i]:
% 0.83/1.07             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.83/1.07               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.83/1.07  thf('9', plain,
% 0.83/1.07      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.83/1.07         ((v2_struct_0 @ X4)
% 0.83/1.07          | ~ (m1_pre_topc @ X4 @ X5)
% 0.83/1.07          | (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.83/1.07          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 0.83/1.07          | ~ (l1_pre_topc @ X5)
% 0.83/1.07          | (v2_struct_0 @ X5))),
% 0.83/1.07      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.83/1.07  thf('10', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         ((v2_struct_0 @ X0)
% 0.83/1.07          | ~ (l1_struct_0 @ X0)
% 0.83/1.07          | ~ (v7_struct_0 @ X0)
% 0.83/1.07          | (v2_struct_0 @ X1)
% 0.83/1.07          | ~ (l1_pre_topc @ X1)
% 0.83/1.07          | (m1_subset_1 @ (sk_B @ X0) @ (u1_struct_0 @ X1))
% 0.83/1.07          | ~ (m1_pre_topc @ X0 @ X1)
% 0.83/1.07          | (v2_struct_0 @ X0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['8', '9'])).
% 0.83/1.07  thf('11', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         (~ (m1_pre_topc @ X0 @ X1)
% 0.83/1.07          | (m1_subset_1 @ (sk_B @ X0) @ (u1_struct_0 @ X1))
% 0.83/1.07          | ~ (l1_pre_topc @ X1)
% 0.83/1.07          | (v2_struct_0 @ X1)
% 0.83/1.07          | ~ (v7_struct_0 @ X0)
% 0.83/1.07          | ~ (l1_struct_0 @ X0)
% 0.83/1.07          | (v2_struct_0 @ X0))),
% 0.83/1.07      inference('simplify', [status(thm)], ['10'])).
% 0.83/1.07  thf('12', plain,
% 0.83/1.07      (((v2_struct_0 @ sk_B_1)
% 0.83/1.07        | ~ (l1_struct_0 @ sk_B_1)
% 0.83/1.07        | ~ (v7_struct_0 @ sk_B_1)
% 0.83/1.07        | (v2_struct_0 @ sk_A)
% 0.83/1.07        | ~ (l1_pre_topc @ sk_A)
% 0.83/1.07        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['7', '11'])).
% 0.83/1.07  thf('13', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf(dt_m1_pre_topc, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( l1_pre_topc @ A ) =>
% 0.83/1.07       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.83/1.07  thf('14', plain,
% 0.83/1.07      (![X1 : $i, X2 : $i]:
% 0.83/1.07         (~ (m1_pre_topc @ X1 @ X2) | (l1_pre_topc @ X1) | ~ (l1_pre_topc @ X2))),
% 0.83/1.07      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.83/1.07  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.83/1.07      inference('sup-', [status(thm)], ['13', '14'])).
% 0.83/1.07  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('17', plain, ((l1_pre_topc @ sk_B_1)),
% 0.83/1.07      inference('demod', [status(thm)], ['15', '16'])).
% 0.83/1.07  thf(dt_l1_pre_topc, axiom,
% 0.83/1.07    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.83/1.07  thf('18', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.83/1.07      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.83/1.07  thf('19', plain, ((l1_struct_0 @ sk_B_1)),
% 0.83/1.07      inference('sup-', [status(thm)], ['17', '18'])).
% 0.83/1.07  thf('20', plain, ((v7_struct_0 @ sk_B_1)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('22', plain,
% 0.83/1.07      (((v2_struct_0 @ sk_B_1)
% 0.83/1.07        | (v2_struct_0 @ sk_A)
% 0.83/1.07        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['12', '19', '20', '21'])).
% 0.83/1.07  thf('23', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('24', plain,
% 0.83/1.07      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.83/1.07        | (v2_struct_0 @ sk_A))),
% 0.83/1.07      inference('clc', [status(thm)], ['22', '23'])).
% 0.83/1.07  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('26', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('clc', [status(thm)], ['24', '25'])).
% 0.83/1.07  thf(dt_k1_tex_2, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.83/1.07         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.07       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.83/1.07         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.83/1.07         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.83/1.07  thf('27', plain,
% 0.83/1.07      (![X17 : $i, X18 : $i]:
% 0.83/1.07         (~ (l1_pre_topc @ X17)
% 0.83/1.07          | (v2_struct_0 @ X17)
% 0.83/1.07          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.83/1.07          | (m1_pre_topc @ (k1_tex_2 @ X17 @ X18) @ X17))),
% 0.83/1.07      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.83/1.07  thf('28', plain,
% 0.83/1.07      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)
% 0.83/1.07        | (v2_struct_0 @ sk_A)
% 0.83/1.07        | ~ (l1_pre_topc @ sk_A))),
% 0.83/1.07      inference('sup-', [status(thm)], ['26', '27'])).
% 0.83/1.07  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('30', plain,
% 0.83/1.07      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)
% 0.83/1.07        | (v2_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['28', '29'])).
% 0.83/1.07  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('32', plain,
% 0.83/1.07      ((m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.83/1.07      inference('clc', [status(thm)], ['30', '31'])).
% 0.83/1.07  thf('33', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('clc', [status(thm)], ['24', '25'])).
% 0.83/1.07  thf('34', plain,
% 0.83/1.07      (![X7 : $i, X8 : $i]:
% 0.83/1.07         ((v1_xboole_0 @ X7)
% 0.83/1.07          | ~ (m1_subset_1 @ X8 @ X7)
% 0.83/1.07          | ((k6_domain_1 @ X7 @ X8) = (k1_tarski @ X8)))),
% 0.83/1.07      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.83/1.07  thf('35', plain,
% 0.83/1.07      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.83/1.07          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.83/1.07        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['33', '34'])).
% 0.83/1.07  thf('36', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('clc', [status(thm)], ['24', '25'])).
% 0.83/1.07  thf('37', plain,
% 0.83/1.07      (![X17 : $i, X18 : $i]:
% 0.83/1.07         (~ (l1_pre_topc @ X17)
% 0.83/1.07          | (v2_struct_0 @ X17)
% 0.83/1.07          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.83/1.07          | (v1_pre_topc @ (k1_tex_2 @ X17 @ X18)))),
% 0.83/1.07      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.83/1.07  thf('38', plain,
% 0.83/1.07      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 0.83/1.07        | (v2_struct_0 @ sk_A)
% 0.83/1.07        | ~ (l1_pre_topc @ sk_A))),
% 0.83/1.07      inference('sup-', [status(thm)], ['36', '37'])).
% 0.83/1.07  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('40', plain,
% 0.83/1.07      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 0.83/1.07        | (v2_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['38', '39'])).
% 0.83/1.07  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('42', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))),
% 0.83/1.07      inference('clc', [status(thm)], ['40', '41'])).
% 0.83/1.07  thf(d4_tex_2, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.07       ( ![B:$i]:
% 0.83/1.07         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.83/1.07           ( ![C:$i]:
% 0.83/1.07             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.83/1.07                 ( m1_pre_topc @ C @ A ) ) =>
% 0.83/1.07               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.83/1.07                 ( ( u1_struct_0 @ C ) =
% 0.83/1.07                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.83/1.07  thf('43', plain,
% 0.83/1.07      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.83/1.07          | ((X16) != (k1_tex_2 @ X15 @ X14))
% 0.83/1.07          | ((u1_struct_0 @ X16) = (k6_domain_1 @ (u1_struct_0 @ X15) @ X14))
% 0.83/1.07          | ~ (m1_pre_topc @ X16 @ X15)
% 0.83/1.07          | ~ (v1_pre_topc @ X16)
% 0.83/1.07          | (v2_struct_0 @ X16)
% 0.83/1.07          | ~ (l1_pre_topc @ X15)
% 0.83/1.07          | (v2_struct_0 @ X15))),
% 0.83/1.07      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.83/1.07  thf('44', plain,
% 0.83/1.07      (![X14 : $i, X15 : $i]:
% 0.83/1.07         ((v2_struct_0 @ X15)
% 0.83/1.07          | ~ (l1_pre_topc @ X15)
% 0.83/1.07          | (v2_struct_0 @ (k1_tex_2 @ X15 @ X14))
% 0.83/1.07          | ~ (v1_pre_topc @ (k1_tex_2 @ X15 @ X14))
% 0.83/1.07          | ~ (m1_pre_topc @ (k1_tex_2 @ X15 @ X14) @ X15)
% 0.83/1.07          | ((u1_struct_0 @ (k1_tex_2 @ X15 @ X14))
% 0.83/1.07              = (k6_domain_1 @ (u1_struct_0 @ X15) @ X14))
% 0.83/1.07          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15)))),
% 0.83/1.07      inference('simplify', [status(thm)], ['43'])).
% 0.83/1.07  thf('45', plain,
% 0.83/1.07      ((~ (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.83/1.07        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 0.83/1.07            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)))
% 0.83/1.07        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)
% 0.83/1.07        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 0.83/1.07        | ~ (l1_pre_topc @ sk_A)
% 0.83/1.07        | (v2_struct_0 @ sk_A))),
% 0.83/1.07      inference('sup-', [status(thm)], ['42', '44'])).
% 0.83/1.07  thf('46', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('clc', [status(thm)], ['24', '25'])).
% 0.83/1.07  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('48', plain,
% 0.83/1.07      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 0.83/1.07          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)))
% 0.83/1.07        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)
% 0.83/1.07        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 0.83/1.07        | (v2_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.83/1.07  thf('49', plain,
% 0.83/1.07      ((m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.83/1.07      inference('clc', [status(thm)], ['30', '31'])).
% 0.83/1.07  thf('50', plain,
% 0.83/1.07      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 0.83/1.07          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)))
% 0.83/1.07        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 0.83/1.07        | (v2_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['48', '49'])).
% 0.83/1.07  thf('51', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('clc', [status(thm)], ['24', '25'])).
% 0.83/1.07  thf('52', plain,
% 0.83/1.07      (![X17 : $i, X18 : $i]:
% 0.83/1.07         (~ (l1_pre_topc @ X17)
% 0.83/1.07          | (v2_struct_0 @ X17)
% 0.83/1.07          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.83/1.07          | ~ (v2_struct_0 @ (k1_tex_2 @ X17 @ X18)))),
% 0.83/1.07      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.83/1.07  thf('53', plain,
% 0.83/1.07      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 0.83/1.07        | (v2_struct_0 @ sk_A)
% 0.83/1.07        | ~ (l1_pre_topc @ sk_A))),
% 0.83/1.07      inference('sup-', [status(thm)], ['51', '52'])).
% 0.83/1.07  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('55', plain,
% 0.83/1.07      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 0.83/1.07        | (v2_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['53', '54'])).
% 0.83/1.07  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('57', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))),
% 0.83/1.07      inference('clc', [status(thm)], ['55', '56'])).
% 0.83/1.07  thf('58', plain,
% 0.83/1.07      (((v2_struct_0 @ sk_A)
% 0.83/1.07        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 0.83/1.07            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))))),
% 0.83/1.07      inference('clc', [status(thm)], ['50', '57'])).
% 0.83/1.07  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('60', plain,
% 0.83/1.07      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 0.83/1.07         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)))),
% 0.83/1.07      inference('clc', [status(thm)], ['58', '59'])).
% 0.83/1.07  thf(t5_tsep_1, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( l1_pre_topc @ A ) =>
% 0.83/1.07       ( ![B:$i]:
% 0.83/1.07         ( ( m1_pre_topc @ B @ A ) =>
% 0.83/1.07           ( ![C:$i]:
% 0.83/1.07             ( ( m1_pre_topc @ C @ A ) =>
% 0.83/1.07               ( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ C ) ) =>
% 0.83/1.07                 ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.83/1.07                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) ) ))).
% 0.83/1.07  thf('61', plain,
% 0.83/1.07      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.83/1.07         (~ (m1_pre_topc @ X9 @ X10)
% 0.83/1.07          | ((u1_struct_0 @ X9) != (u1_struct_0 @ X11))
% 0.83/1.07          | ((g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9))
% 0.83/1.07              = (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.83/1.07          | ~ (m1_pre_topc @ X11 @ X10)
% 0.83/1.07          | ~ (l1_pre_topc @ X10))),
% 0.83/1.07      inference('cnf', [status(esa)], [t5_tsep_1])).
% 0.83/1.07  thf('62', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         (((u1_struct_0 @ X0)
% 0.83/1.07            != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)))
% 0.83/1.07          | ~ (l1_pre_topc @ X1)
% 0.83/1.07          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ X1)
% 0.83/1.07          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.83/1.07              = (g1_pre_topc @ 
% 0.83/1.07                 (u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))) @ 
% 0.83/1.07                 (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))))
% 0.83/1.07          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.83/1.07      inference('sup-', [status(thm)], ['60', '61'])).
% 0.83/1.07  thf('63', plain,
% 0.83/1.07      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 0.83/1.07         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)))),
% 0.83/1.07      inference('clc', [status(thm)], ['58', '59'])).
% 0.83/1.07  thf('64', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         (((u1_struct_0 @ X0)
% 0.83/1.07            != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)))
% 0.83/1.07          | ~ (l1_pre_topc @ X1)
% 0.83/1.07          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ X1)
% 0.83/1.07          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.83/1.07              = (g1_pre_topc @ 
% 0.83/1.07                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.83/1.07                 (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))))
% 0.83/1.07          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.83/1.07      inference('demod', [status(thm)], ['62', '63'])).
% 0.83/1.07  thf('65', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         (((u1_struct_0 @ X0) != (k1_tarski @ (sk_B @ sk_B_1)))
% 0.83/1.07          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | ~ (m1_pre_topc @ X0 @ X1)
% 0.83/1.07          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.83/1.07              = (g1_pre_topc @ 
% 0.83/1.07                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.83/1.07                 (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))))
% 0.83/1.07          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)) @ X1)
% 0.83/1.07          | ~ (l1_pre_topc @ X1))),
% 0.83/1.07      inference('sup-', [status(thm)], ['35', '64'])).
% 0.83/1.07  thf('66', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (~ (l1_pre_topc @ sk_A)
% 0.83/1.07          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.83/1.07              = (g1_pre_topc @ 
% 0.83/1.07                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.83/1.07                 (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))))
% 0.83/1.07          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.83/1.07          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | ((u1_struct_0 @ X0) != (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['32', '65'])).
% 0.83/1.07  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('68', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.83/1.07            = (g1_pre_topc @ 
% 0.83/1.07               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.83/1.07               (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))))
% 0.83/1.07          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.83/1.07          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | ((u1_struct_0 @ X0) != (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.83/1.07      inference('demod', [status(thm)], ['66', '67'])).
% 0.83/1.07  thf('69', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (((u1_struct_0 @ X0) != (u1_struct_0 @ sk_B_1))
% 0.83/1.07          | (v2_struct_0 @ sk_B_1)
% 0.83/1.07          | ~ (l1_struct_0 @ sk_B_1)
% 0.83/1.07          | ~ (v7_struct_0 @ sk_B_1)
% 0.83/1.07          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.83/1.07          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.83/1.07          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.83/1.07              = (g1_pre_topc @ 
% 0.83/1.07                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.83/1.07                 (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['6', '68'])).
% 0.83/1.07  thf('70', plain, ((l1_struct_0 @ sk_B_1)),
% 0.83/1.07      inference('sup-', [status(thm)], ['17', '18'])).
% 0.83/1.07  thf('71', plain, ((v7_struct_0 @ sk_B_1)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('72', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (((u1_struct_0 @ X0) != (u1_struct_0 @ sk_B_1))
% 0.83/1.07          | (v2_struct_0 @ sk_B_1)
% 0.83/1.07          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.83/1.07          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.83/1.07          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.83/1.07              = (g1_pre_topc @ 
% 0.83/1.07                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.83/1.07                 (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1))))))),
% 0.83/1.07      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.83/1.07  thf('73', plain,
% 0.83/1.07      ((((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 0.83/1.07          = (g1_pre_topc @ 
% 0.83/1.07             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.83/1.07             (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))))
% 0.83/1.07        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.83/1.07        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.83/1.07        | (v2_struct_0 @ sk_B_1))),
% 0.83/1.07      inference('eq_res', [status(thm)], ['72'])).
% 0.83/1.07  thf('74', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('75', plain,
% 0.83/1.07      ((((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 0.83/1.07          = (g1_pre_topc @ 
% 0.83/1.07             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.83/1.07             (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))))
% 0.83/1.07        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.83/1.07        | (v2_struct_0 @ sk_B_1))),
% 0.83/1.07      inference('demod', [status(thm)], ['73', '74'])).
% 0.83/1.07  thf('76', plain,
% 0.83/1.07      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))
% 0.83/1.07         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)))),
% 0.83/1.07      inference('clc', [status(thm)], ['58', '59'])).
% 0.83/1.07  thf('77', plain,
% 0.83/1.07      (![X19 : $i]:
% 0.83/1.07         (((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 0.83/1.07            != (g1_pre_topc @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ X19)) @ 
% 0.83/1.07                (u1_pre_topc @ (k1_tex_2 @ sk_A @ X19))))
% 0.83/1.07          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('78', plain,
% 0.83/1.07      ((((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 0.83/1.07          != (g1_pre_topc @ 
% 0.83/1.07              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.83/1.07              (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))))
% 0.83/1.07        | ~ (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['76', '77'])).
% 0.83/1.07  thf('79', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.83/1.07      inference('clc', [status(thm)], ['24', '25'])).
% 0.83/1.07  thf('80', plain,
% 0.83/1.07      (((g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 0.83/1.07         != (g1_pre_topc @ 
% 0.83/1.07             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.83/1.07             (u1_pre_topc @ (k1_tex_2 @ sk_A @ (sk_B @ sk_B_1)))))),
% 0.83/1.07      inference('demod', [status(thm)], ['78', '79'])).
% 0.83/1.07  thf('81', plain,
% 0.83/1.07      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.83/1.07        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.83/1.07        | (v2_struct_0 @ sk_B_1))),
% 0.83/1.07      inference('simplify_reflect-', [status(thm)], ['75', '80'])).
% 0.83/1.07  thf('82', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('83', plain,
% 0.83/1.07      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.83/1.07        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.07      inference('clc', [status(thm)], ['81', '82'])).
% 0.83/1.07  thf(fc2_struct_0, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.83/1.07       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.83/1.07  thf('84', plain,
% 0.83/1.07      (![X3 : $i]:
% 0.83/1.07         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 0.83/1.07          | ~ (l1_struct_0 @ X3)
% 0.83/1.07          | (v2_struct_0 @ X3))),
% 0.83/1.07      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.83/1.07  thf('85', plain,
% 0.83/1.07      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.83/1.07        | (v2_struct_0 @ sk_A)
% 0.83/1.07        | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.07      inference('sup-', [status(thm)], ['83', '84'])).
% 0.83/1.07  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('87', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.83/1.07      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.83/1.07  thf('88', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.07      inference('sup-', [status(thm)], ['86', '87'])).
% 0.83/1.07  thf('89', plain,
% 0.83/1.07      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['85', '88'])).
% 0.83/1.07  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('91', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.83/1.07      inference('clc', [status(thm)], ['89', '90'])).
% 0.83/1.07  thf('92', plain,
% 0.83/1.07      (![X3 : $i]:
% 0.83/1.07         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 0.83/1.07          | ~ (l1_struct_0 @ X3)
% 0.83/1.07          | (v2_struct_0 @ X3))),
% 0.83/1.07      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.83/1.07  thf('93', plain, (((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1))),
% 0.83/1.07      inference('sup-', [status(thm)], ['91', '92'])).
% 0.83/1.07  thf('94', plain, ((l1_struct_0 @ sk_B_1)),
% 0.83/1.07      inference('sup-', [status(thm)], ['17', '18'])).
% 0.83/1.07  thf('95', plain, ((v2_struct_0 @ sk_B_1)),
% 0.83/1.07      inference('demod', [status(thm)], ['93', '94'])).
% 0.83/1.07  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 0.83/1.07  
% 0.83/1.07  % SZS output end Refutation
% 0.83/1.07  
% 0.83/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
