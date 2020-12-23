%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7ONGj6aF2k

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:01 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 188 expanded)
%              Number of leaves         :   29 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  840 (2232 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t20_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
          <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
            <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_tex_2])).

thf('0',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ X4 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13 = X12 )
      | ( v1_subset_1 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
       != ( k6_domain_1 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( v1_zfmisc_1 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('10',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(cc1_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_zfmisc_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_zfmisc_1])).

thf('15',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('16',plain,(
    ! [X3: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v7_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('17',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('19',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('26',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf(cc10_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v7_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ~ ( v2_struct_0 @ B )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tex_2 @ B @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ~ ( v1_tex_2 @ X6 @ X7 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v7_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc10_tex_2])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('38',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['35','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','45'])).

thf('47',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['22'])).

thf('48',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf(cc13_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ~ ( v7_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tex_2 @ B @ A ) )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v7_struct_0 @ B ) ) ) ) ) )).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( v7_struct_0 @ X8 )
      | ( v1_tex_2 @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v7_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc13_tex_2])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('54',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','58'])).

thf('60',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('63',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('67',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v7_struct_0 @ X19 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('70',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['65','73'])).

thf('75',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','46','47','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7ONGj6aF2k
% 0.18/0.38  % Computer   : n014.cluster.edu
% 0.18/0.38  % Model      : x86_64 x86_64
% 0.18/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.38  % Memory     : 8042.1875MB
% 0.18/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.38  % CPULimit   : 60
% 0.18/0.38  % DateTime   : Tue Dec  1 10:58:53 EST 2020
% 0.18/0.38  % CPUTime    : 
% 0.18/0.38  % Running portfolio for 600 s
% 0.18/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.38  % Number of cores: 8
% 0.18/0.38  % Python version: Python 3.6.8
% 0.18/0.38  % Running in FO mode
% 0.25/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.52  % Solved by: fo/fo7.sh
% 0.25/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.52  % done 81 iterations in 0.033s
% 0.25/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.52  % SZS output start Refutation
% 0.25/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.25/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.25/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.25/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.25/0.52  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.25/0.52  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.25/0.52  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.25/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.25/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.25/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.25/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.52  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.25/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.25/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.25/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.52  thf(t20_tex_2, conjecture,
% 0.25/0.52    (![A:$i]:
% 0.25/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.52       ( ![B:$i]:
% 0.25/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.25/0.52           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.25/0.52             ( v1_subset_1 @
% 0.25/0.52               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.25/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.52    (~( ![A:$i]:
% 0.25/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.52          ( ![B:$i]:
% 0.25/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.25/0.52              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.25/0.52                ( v1_subset_1 @
% 0.25/0.52                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.25/0.52                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.25/0.52    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.25/0.52  thf('0', plain,
% 0.25/0.52      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52           (u1_struct_0 @ sk_A))
% 0.25/0.52        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('1', plain,
% 0.25/0.52      (~
% 0.25/0.52       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52         (u1_struct_0 @ sk_A))) | 
% 0.25/0.52       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.25/0.52      inference('split', [status(esa)], ['0'])).
% 0.25/0.52  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(dt_k6_domain_1, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.25/0.52       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.25/0.52  thf('3', plain,
% 0.25/0.52      (![X4 : $i, X5 : $i]:
% 0.25/0.52         ((v1_xboole_0 @ X4)
% 0.25/0.52          | ~ (m1_subset_1 @ X5 @ X4)
% 0.25/0.52          | (m1_subset_1 @ (k6_domain_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4)))),
% 0.25/0.52      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.25/0.52  thf('4', plain,
% 0.25/0.52      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.25/0.52  thf(d7_subset_1, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.25/0.52       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.25/0.52  thf('5', plain,
% 0.25/0.52      (![X12 : $i, X13 : $i]:
% 0.25/0.52         (((X13) = (X12))
% 0.25/0.52          | (v1_subset_1 @ X13 @ X12)
% 0.25/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.25/0.52      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.25/0.52  thf('6', plain,
% 0.25/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.52        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52           (u1_struct_0 @ sk_A))
% 0.25/0.52        | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.25/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.25/0.52  thf('7', plain,
% 0.25/0.52      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52           (u1_struct_0 @ sk_A)))
% 0.25/0.52         <= (~
% 0.25/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52               (u1_struct_0 @ sk_A))))),
% 0.25/0.52      inference('split', [status(esa)], ['0'])).
% 0.25/0.52  thf('8', plain,
% 0.25/0.52      (((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.25/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.25/0.52         <= (~
% 0.25/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52               (u1_struct_0 @ sk_A))))),
% 0.25/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.25/0.52  thf(d1_tex_2, axiom,
% 0.25/0.52    (![A:$i]:
% 0.25/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.25/0.52       ( ( v1_zfmisc_1 @ A ) <=>
% 0.25/0.52         ( ?[B:$i]:
% 0.25/0.52           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.25/0.52  thf('9', plain,
% 0.25/0.52      (![X10 : $i, X11 : $i]:
% 0.25/0.52         (((X10) != (k6_domain_1 @ X10 @ X11))
% 0.25/0.52          | ~ (m1_subset_1 @ X11 @ X10)
% 0.25/0.52          | (v1_zfmisc_1 @ X10)
% 0.25/0.52          | (v1_xboole_0 @ X10))),
% 0.25/0.52      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.25/0.52  thf('10', plain,
% 0.25/0.52      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.25/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.52         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.25/0.52         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.25/0.52         <= (~
% 0.25/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52               (u1_struct_0 @ sk_A))))),
% 0.25/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.25/0.52  thf('11', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('12', plain,
% 0.25/0.52      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.25/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.25/0.52         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.25/0.52         <= (~
% 0.25/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52               (u1_struct_0 @ sk_A))))),
% 0.25/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.25/0.52  thf('13', plain,
% 0.25/0.52      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.25/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.25/0.52         <= (~
% 0.25/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52               (u1_struct_0 @ sk_A))))),
% 0.25/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.25/0.52  thf(cc1_zfmisc_1, axiom,
% 0.25/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.25/0.52  thf('14', plain, (![X0 : $i]: ((v1_zfmisc_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.25/0.52      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.25/0.52  thf('15', plain,
% 0.25/0.52      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.52         <= (~
% 0.25/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52               (u1_struct_0 @ sk_A))))),
% 0.25/0.52      inference('clc', [status(thm)], ['13', '14'])).
% 0.25/0.52  thf(fc6_struct_0, axiom,
% 0.25/0.52    (![A:$i]:
% 0.25/0.52     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.25/0.52       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.25/0.52  thf('16', plain,
% 0.25/0.52      (![X3 : $i]:
% 0.25/0.52         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X3))
% 0.25/0.52          | ~ (l1_struct_0 @ X3)
% 0.25/0.52          | (v7_struct_0 @ X3))),
% 0.25/0.52      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.25/0.52  thf('17', plain,
% 0.25/0.52      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.25/0.52         <= (~
% 0.25/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52               (u1_struct_0 @ sk_A))))),
% 0.25/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.25/0.52  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(dt_l1_pre_topc, axiom,
% 0.25/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.25/0.52  thf('19', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.25/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.25/0.52  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.25/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.25/0.52  thf('21', plain,
% 0.25/0.52      (((v7_struct_0 @ sk_A))
% 0.25/0.52         <= (~
% 0.25/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52               (u1_struct_0 @ sk_A))))),
% 0.25/0.52      inference('demod', [status(thm)], ['17', '20'])).
% 0.25/0.52  thf('22', plain,
% 0.25/0.52      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52         (u1_struct_0 @ sk_A))
% 0.25/0.52        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('23', plain,
% 0.25/0.52      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.25/0.52         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.25/0.52      inference('split', [status(esa)], ['22'])).
% 0.25/0.52  thf('24', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(dt_k1_tex_2, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.25/0.52         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.52       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.25/0.52         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.25/0.52         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.25/0.52  thf('25', plain,
% 0.25/0.52      (![X14 : $i, X15 : $i]:
% 0.25/0.52         (~ (l1_pre_topc @ X14)
% 0.25/0.52          | (v2_struct_0 @ X14)
% 0.25/0.52          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.25/0.52          | (m1_pre_topc @ (k1_tex_2 @ X14 @ X15) @ X14))),
% 0.25/0.52      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.25/0.52  thf('26', plain,
% 0.25/0.52      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.25/0.52        | (v2_struct_0 @ sk_A)
% 0.25/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.25/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.25/0.52  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('28', plain,
% 0.25/0.52      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.25/0.52        | (v2_struct_0 @ sk_A))),
% 0.25/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.25/0.52  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('30', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.25/0.52      inference('clc', [status(thm)], ['28', '29'])).
% 0.25/0.52  thf(cc10_tex_2, axiom,
% 0.25/0.52    (![A:$i]:
% 0.25/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.52       ( ![B:$i]:
% 0.25/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.25/0.52           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.25/0.52             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.25/0.52  thf('31', plain,
% 0.25/0.52      (![X6 : $i, X7 : $i]:
% 0.25/0.52         (~ (m1_pre_topc @ X6 @ X7)
% 0.25/0.52          | ~ (v1_tex_2 @ X6 @ X7)
% 0.25/0.52          | (v2_struct_0 @ X6)
% 0.25/0.52          | ~ (l1_pre_topc @ X7)
% 0.25/0.52          | ~ (v7_struct_0 @ X7)
% 0.25/0.52          | (v2_struct_0 @ X7))),
% 0.25/0.52      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.25/0.52  thf('32', plain,
% 0.25/0.52      (((v2_struct_0 @ sk_A)
% 0.25/0.52        | ~ (v7_struct_0 @ sk_A)
% 0.25/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.25/0.52        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.25/0.52        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.25/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.25/0.52  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('34', plain,
% 0.25/0.52      (((v2_struct_0 @ sk_A)
% 0.25/0.52        | ~ (v7_struct_0 @ sk_A)
% 0.25/0.52        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.25/0.52        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.25/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.25/0.52  thf('35', plain,
% 0.25/0.52      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.25/0.52         | ~ (v7_struct_0 @ sk_A)
% 0.25/0.52         | (v2_struct_0 @ sk_A)))
% 0.25/0.52         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.25/0.52      inference('sup-', [status(thm)], ['23', '34'])).
% 0.25/0.52  thf('36', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('37', plain,
% 0.25/0.52      (![X14 : $i, X15 : $i]:
% 0.25/0.52         (~ (l1_pre_topc @ X14)
% 0.25/0.52          | (v2_struct_0 @ X14)
% 0.25/0.52          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.25/0.52          | ~ (v2_struct_0 @ (k1_tex_2 @ X14 @ X15)))),
% 0.25/0.52      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.25/0.52  thf('38', plain,
% 0.25/0.52      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.25/0.52        | (v2_struct_0 @ sk_A)
% 0.25/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.25/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.25/0.52  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('40', plain,
% 0.25/0.52      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.25/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.25/0.52  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('42', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.25/0.52      inference('clc', [status(thm)], ['40', '41'])).
% 0.25/0.52  thf('43', plain,
% 0.25/0.52      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.25/0.52         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.25/0.52      inference('clc', [status(thm)], ['35', '42'])).
% 0.25/0.52  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('45', plain,
% 0.25/0.52      ((~ (v7_struct_0 @ sk_A))
% 0.25/0.52         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.25/0.52      inference('clc', [status(thm)], ['43', '44'])).
% 0.25/0.52  thf('46', plain,
% 0.25/0.52      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52         (u1_struct_0 @ sk_A))) | 
% 0.25/0.52       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.25/0.52      inference('sup-', [status(thm)], ['21', '45'])).
% 0.25/0.52  thf('47', plain,
% 0.25/0.52      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52         (u1_struct_0 @ sk_A))) | 
% 0.25/0.52       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.25/0.52      inference('split', [status(esa)], ['22'])).
% 0.25/0.52  thf('48', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.25/0.52      inference('clc', [status(thm)], ['28', '29'])).
% 0.25/0.52  thf(cc13_tex_2, axiom,
% 0.25/0.52    (![A:$i]:
% 0.25/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( ~( v7_struct_0 @ A ) ) & 
% 0.25/0.52         ( l1_pre_topc @ A ) ) =>
% 0.25/0.52       ( ![B:$i]:
% 0.25/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.25/0.52           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) =>
% 0.25/0.52             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) ) ) ) ))).
% 0.25/0.52  thf('49', plain,
% 0.25/0.52      (![X8 : $i, X9 : $i]:
% 0.25/0.52         (~ (m1_pre_topc @ X8 @ X9)
% 0.25/0.52          | ~ (v7_struct_0 @ X8)
% 0.25/0.52          | (v1_tex_2 @ X8 @ X9)
% 0.25/0.52          | (v2_struct_0 @ X8)
% 0.25/0.52          | ~ (l1_pre_topc @ X9)
% 0.25/0.52          | (v7_struct_0 @ X9)
% 0.25/0.52          | (v2_struct_0 @ X9))),
% 0.25/0.52      inference('cnf', [status(esa)], [cc13_tex_2])).
% 0.25/0.52  thf('50', plain,
% 0.25/0.52      (((v2_struct_0 @ sk_A)
% 0.25/0.52        | (v7_struct_0 @ sk_A)
% 0.25/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.25/0.52        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.25/0.52        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.25/0.52        | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.25/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.25/0.52  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('52', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(fc2_tex_2, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.25/0.52         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.52       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.25/0.52         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.25/0.52         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.25/0.52  thf('53', plain,
% 0.25/0.52      (![X16 : $i, X17 : $i]:
% 0.25/0.52         (~ (l1_pre_topc @ X16)
% 0.25/0.52          | (v2_struct_0 @ X16)
% 0.25/0.52          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.25/0.52          | (v7_struct_0 @ (k1_tex_2 @ X16 @ X17)))),
% 0.25/0.52      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.25/0.52  thf('54', plain,
% 0.25/0.52      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.25/0.52        | (v2_struct_0 @ sk_A)
% 0.25/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.25/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.25/0.52  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('56', plain,
% 0.25/0.52      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.25/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.25/0.52  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('58', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.25/0.52      inference('clc', [status(thm)], ['56', '57'])).
% 0.25/0.52  thf('59', plain,
% 0.25/0.52      (((v2_struct_0 @ sk_A)
% 0.25/0.52        | (v7_struct_0 @ sk_A)
% 0.25/0.52        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.25/0.52        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.25/0.52      inference('demod', [status(thm)], ['50', '51', '58'])).
% 0.25/0.52  thf('60', plain,
% 0.25/0.52      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.25/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.25/0.52      inference('split', [status(esa)], ['0'])).
% 0.25/0.52  thf('61', plain,
% 0.25/0.52      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.25/0.52         | (v7_struct_0 @ sk_A)
% 0.25/0.52         | (v2_struct_0 @ sk_A)))
% 0.25/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.25/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.25/0.52  thf('62', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.25/0.52      inference('clc', [status(thm)], ['40', '41'])).
% 0.25/0.52  thf('63', plain,
% 0.25/0.52      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ sk_A)))
% 0.25/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.25/0.52      inference('clc', [status(thm)], ['61', '62'])).
% 0.25/0.52  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('65', plain,
% 0.25/0.52      (((v7_struct_0 @ sk_A))
% 0.25/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.25/0.52      inference('clc', [status(thm)], ['63', '64'])).
% 0.25/0.52  thf('66', plain,
% 0.25/0.52      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52         (u1_struct_0 @ sk_A)))
% 0.25/0.52         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52               (u1_struct_0 @ sk_A))))),
% 0.25/0.52      inference('split', [status(esa)], ['22'])).
% 0.25/0.52  thf(t8_tex_2, axiom,
% 0.25/0.52    (![A:$i]:
% 0.25/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.25/0.52       ( ![B:$i]:
% 0.25/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.25/0.52           ( ~( ( v1_subset_1 @
% 0.25/0.52                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.25/0.52                  ( u1_struct_0 @ A ) ) & 
% 0.25/0.52                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.25/0.52  thf('67', plain,
% 0.25/0.52      (![X18 : $i, X19 : $i]:
% 0.25/0.52         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.25/0.52          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X19) @ X18) @ 
% 0.25/0.52               (u1_struct_0 @ X19))
% 0.25/0.52          | ~ (v7_struct_0 @ X19)
% 0.25/0.52          | ~ (l1_struct_0 @ X19)
% 0.25/0.52          | (v2_struct_0 @ X19))),
% 0.25/0.52      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.25/0.52  thf('68', plain,
% 0.25/0.52      ((((v2_struct_0 @ sk_A)
% 0.25/0.52         | ~ (l1_struct_0 @ sk_A)
% 0.25/0.52         | ~ (v7_struct_0 @ sk_A)
% 0.25/0.52         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.25/0.52         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52               (u1_struct_0 @ sk_A))))),
% 0.25/0.52      inference('sup-', [status(thm)], ['66', '67'])).
% 0.25/0.52  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.25/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.25/0.52  thf('70', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('71', plain,
% 0.25/0.52      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.25/0.52         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52               (u1_struct_0 @ sk_A))))),
% 0.25/0.52      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.25/0.52  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('73', plain,
% 0.25/0.52      ((~ (v7_struct_0 @ sk_A))
% 0.25/0.52         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52               (u1_struct_0 @ sk_A))))),
% 0.25/0.52      inference('clc', [status(thm)], ['71', '72'])).
% 0.25/0.52  thf('74', plain,
% 0.25/0.52      (~
% 0.25/0.52       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.25/0.52         (u1_struct_0 @ sk_A))) | 
% 0.25/0.52       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.25/0.52      inference('sup-', [status(thm)], ['65', '73'])).
% 0.25/0.52  thf('75', plain, ($false),
% 0.25/0.52      inference('sat_resolution*', [status(thm)], ['1', '46', '47', '74'])).
% 0.25/0.52  
% 0.25/0.52  % SZS output end Refutation
% 0.25/0.52  
% 0.25/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
