%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3qh83QFiaK

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:03 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 260 expanded)
%              Number of leaves         :   32 (  84 expanded)
%              Depth                    :   19
%              Number of atoms          : 1118 (3114 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( X16 = X15 )
      | ( v1_subset_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
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
    ! [X4: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v7_struct_0 @ X4 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X17 @ X18 ) @ X17 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( v1_tex_2 @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v7_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X17 @ X18 ) ) ) ),
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

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( ( sk_C @ X12 @ X13 )
        = ( u1_struct_0 @ X12 ) )
      | ( v1_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_C @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 = X15 )
      | ( v1_subset_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('61',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( v1_subset_1 @ ( sk_C @ X12 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ( v1_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('63',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf('66',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('69',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['54','69'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('71',plain,(
    ! [X5: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ~ ( v7_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('72',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
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

thf('74',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('75',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('81',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('82',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('86',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['72','79','86'])).

thf('88',plain,(
    ! [X4: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v7_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('89',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('91',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
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

thf('93',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v7_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','46','47','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3qh83QFiaK
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:08:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 114 iterations in 0.103s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.37/0.55  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.37/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.55  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.37/0.55  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.37/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.37/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.55  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.37/0.55  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(t20_tex_2, conjecture,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.55           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.37/0.55             ( v1_subset_1 @
% 0.37/0.55               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i]:
% 0.37/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.55          ( ![B:$i]:
% 0.37/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.55              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.37/0.55                ( v1_subset_1 @
% 0.37/0.55                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.37/0.55                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55           (u1_struct_0 @ sk_A))
% 0.37/0.55        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (~
% 0.37/0.55       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55         (u1_struct_0 @ sk_A))) | 
% 0.37/0.55       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(dt_k6_domain_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.37/0.55       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X6 : $i, X7 : $i]:
% 0.37/0.55         ((v1_xboole_0 @ X6)
% 0.37/0.55          | ~ (m1_subset_1 @ X7 @ X6)
% 0.37/0.55          | (m1_subset_1 @ (k6_domain_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.55  thf(d7_subset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i]:
% 0.37/0.55         (((X16) = (X15))
% 0.37/0.55          | (v1_subset_1 @ X16 @ X15)
% 0.37/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55           (u1_struct_0 @ sk_A))
% 0.37/0.55        | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55           (u1_struct_0 @ sk_A)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55               (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55               (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.55  thf(d1_tex_2, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.55       ( ( v1_zfmisc_1 @ A ) <=>
% 0.37/0.55         ( ?[B:$i]:
% 0.37/0.55           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i]:
% 0.37/0.55         (((X10) != (k6_domain_1 @ X10 @ X11))
% 0.37/0.55          | ~ (m1_subset_1 @ X11 @ X10)
% 0.37/0.55          | (v1_zfmisc_1 @ X10)
% 0.37/0.55          | (v1_xboole_0 @ X10))),
% 0.37/0.55      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55               (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.55  thf('11', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55               (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.37/0.55         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55               (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.37/0.55  thf(cc1_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.37/0.55  thf('14', plain, (![X0 : $i]: ((v1_zfmisc_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55               (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('clc', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf(fc6_struct_0, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.55       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X4 : $i]:
% 0.37/0.55         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X4))
% 0.37/0.55          | ~ (l1_struct_0 @ X4)
% 0.37/0.55          | (v7_struct_0 @ X4))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55               (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(dt_l1_pre_topc, axiom,
% 0.37/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.37/0.55  thf('19', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.55  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (((v7_struct_0 @ sk_A))
% 0.37/0.55         <= (~
% 0.37/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55               (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['17', '20'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55         (u1_struct_0 @ sk_A))
% 0.37/0.55        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.37/0.55         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.37/0.55      inference('split', [status(esa)], ['22'])).
% 0.37/0.55  thf('24', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(dt_k1_tex_2, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.37/0.55         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.37/0.55         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.37/0.55         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X17 : $i, X18 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ X17)
% 0.37/0.55          | (v2_struct_0 @ X17)
% 0.37/0.55          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.37/0.55          | (m1_pre_topc @ (k1_tex_2 @ X17 @ X18) @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.55  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.37/0.55        | (v2_struct_0 @ sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('30', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.37/0.55      inference('clc', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf(cc10_tex_2, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.55           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.37/0.55             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i]:
% 0.37/0.55         (~ (m1_pre_topc @ X8 @ X9)
% 0.37/0.55          | ~ (v1_tex_2 @ X8 @ X9)
% 0.37/0.55          | (v2_struct_0 @ X8)
% 0.37/0.55          | ~ (l1_pre_topc @ X9)
% 0.37/0.55          | ~ (v7_struct_0 @ X9)
% 0.37/0.55          | (v2_struct_0 @ X9))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (((v2_struct_0 @ sk_A)
% 0.37/0.55        | ~ (v7_struct_0 @ sk_A)
% 0.37/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.37/0.55        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.55  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (((v2_struct_0 @ sk_A)
% 0.37/0.55        | ~ (v7_struct_0 @ sk_A)
% 0.37/0.55        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.37/0.55        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.37/0.55         | ~ (v7_struct_0 @ sk_A)
% 0.37/0.55         | (v2_struct_0 @ sk_A)))
% 0.37/0.55         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['23', '34'])).
% 0.37/0.55  thf('36', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      (![X17 : $i, X18 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ X17)
% 0.37/0.55          | (v2_struct_0 @ X17)
% 0.37/0.55          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.37/0.55          | ~ (v2_struct_0 @ (k1_tex_2 @ X17 @ X18)))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.37/0.55        | (v2_struct_0 @ sk_A)
% 0.37/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.55  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['38', '39'])).
% 0.37/0.55  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('42', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.37/0.55      inference('clc', [status(thm)], ['40', '41'])).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.37/0.55         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.37/0.55      inference('clc', [status(thm)], ['35', '42'])).
% 0.37/0.55  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('45', plain,
% 0.37/0.55      ((~ (v7_struct_0 @ sk_A))
% 0.37/0.55         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.37/0.55      inference('clc', [status(thm)], ['43', '44'])).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55         (u1_struct_0 @ sk_A))) | 
% 0.37/0.55       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '45'])).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.55         (u1_struct_0 @ sk_A))) | 
% 0.37/0.55       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.37/0.55      inference('split', [status(esa)], ['22'])).
% 0.37/0.55  thf('48', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.37/0.55      inference('clc', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf(d3_tex_2, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_pre_topc @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.55           ( ( v1_tex_2 @ B @ A ) <=>
% 0.37/0.55             ( ![C:$i]:
% 0.37/0.55               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.37/0.55                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         (~ (m1_pre_topc @ X12 @ X13)
% 0.37/0.55          | ((sk_C @ X12 @ X13) = (u1_struct_0 @ X12))
% 0.37/0.55          | (v1_tex_2 @ X12 @ X13)
% 0.37/0.55          | ~ (l1_pre_topc @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.37/0.55  thf('50', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.37/0.55        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.37/0.55            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.55  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.37/0.55        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.37/0.55            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.37/0.55      inference('demod', [status(thm)], ['50', '51'])).
% 0.37/0.55  thf('53', plain,
% 0.37/0.55      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.37/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.37/0.56          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.37/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.56  thf('55', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.37/0.56      inference('clc', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X12 @ X13)
% 0.37/0.56          | (m1_subset_1 @ (sk_C @ X12 @ X13) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.37/0.56          | (v1_tex_2 @ X12 @ X13)
% 0.37/0.56          | ~ (l1_pre_topc @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.37/0.56        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.37/0.56  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.37/0.56        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['57', '58'])).
% 0.37/0.56  thf('60', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i]:
% 0.37/0.56         (((X16) = (X15))
% 0.37/0.56          | (v1_subset_1 @ X16 @ X15)
% 0.37/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.37/0.56        | (v1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A) @ 
% 0.37/0.56           (u1_struct_0 @ sk_A))
% 0.37/0.56        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X12 @ X13)
% 0.37/0.56          | ~ (v1_subset_1 @ (sk_C @ X12 @ X13) @ (u1_struct_0 @ X13))
% 0.37/0.56          | (v1_tex_2 @ X12 @ X13)
% 0.37/0.56          | ~ (l1_pre_topc @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A) = (u1_struct_0 @ sk_A))
% 0.37/0.56        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.37/0.56        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.56  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('65', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.37/0.56      inference('clc', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf('66', plain,
% 0.37/0.56      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A) = (u1_struct_0 @ sk_A))
% 0.37/0.56        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.37/0.56        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.37/0.56  thf('67', plain,
% 0.37/0.56      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.37/0.56        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['66'])).
% 0.37/0.56  thf('68', plain,
% 0.37/0.56      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.37/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.37/0.56      inference('split', [status(esa)], ['0'])).
% 0.37/0.56  thf('69', plain,
% 0.37/0.56      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.37/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.37/0.56  thf('70', plain,
% 0.37/0.56      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.37/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['54', '69'])).
% 0.37/0.56  thf(fc7_struct_0, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.56       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.37/0.56  thf('71', plain,
% 0.37/0.56      (![X5 : $i]:
% 0.37/0.56         ((v1_zfmisc_1 @ (u1_struct_0 @ X5))
% 0.37/0.56          | ~ (l1_struct_0 @ X5)
% 0.37/0.56          | ~ (v7_struct_0 @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.37/0.56  thf('72', plain,
% 0.37/0.56      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.37/0.56         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.37/0.56         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.37/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['70', '71'])).
% 0.37/0.56  thf('73', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(fc2_tex_2, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.37/0.56         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.37/0.56         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.37/0.56         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.37/0.56  thf('74', plain,
% 0.37/0.56      (![X19 : $i, X20 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X19)
% 0.37/0.56          | (v2_struct_0 @ X19)
% 0.37/0.56          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.37/0.56          | (v7_struct_0 @ (k1_tex_2 @ X19 @ X20)))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.37/0.56  thf('75', plain,
% 0.37/0.56      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['73', '74'])).
% 0.37/0.56  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('77', plain,
% 0.37/0.56      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.56  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('79', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.37/0.56      inference('clc', [status(thm)], ['77', '78'])).
% 0.37/0.56  thf('80', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.37/0.56      inference('clc', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf(dt_m1_pre_topc, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.37/0.56  thf('81', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.37/0.56  thf('82', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['80', '81'])).
% 0.37/0.56  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('84', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.37/0.56      inference('demod', [status(thm)], ['82', '83'])).
% 0.37/0.56  thf('85', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('86', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['84', '85'])).
% 0.37/0.56  thf('87', plain,
% 0.37/0.56      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['72', '79', '86'])).
% 0.37/0.56  thf('88', plain,
% 0.37/0.56      (![X4 : $i]:
% 0.37/0.56         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X4))
% 0.37/0.56          | ~ (l1_struct_0 @ X4)
% 0.37/0.56          | (v7_struct_0 @ X4))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.37/0.56  thf('89', plain,
% 0.37/0.56      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.37/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['87', '88'])).
% 0.37/0.56  thf('90', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf('91', plain,
% 0.37/0.56      (((v7_struct_0 @ sk_A))
% 0.37/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['89', '90'])).
% 0.37/0.56  thf('92', plain,
% 0.37/0.56      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.56         (u1_struct_0 @ sk_A)))
% 0.37/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.56               (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('split', [status(esa)], ['22'])).
% 0.37/0.56  thf(t8_tex_2, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56           ( ~( ( v1_subset_1 @
% 0.37/0.56                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.37/0.56                  ( u1_struct_0 @ A ) ) & 
% 0.37/0.56                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.56  thf('93', plain,
% 0.37/0.56      (![X21 : $i, X22 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.37/0.56          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X22) @ X21) @ 
% 0.37/0.56               (u1_struct_0 @ X22))
% 0.37/0.56          | ~ (v7_struct_0 @ X22)
% 0.37/0.56          | ~ (l1_struct_0 @ X22)
% 0.37/0.56          | (v2_struct_0 @ X22))),
% 0.37/0.56      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.37/0.56  thf('94', plain,
% 0.37/0.56      ((((v2_struct_0 @ sk_A)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.37/0.56         | ~ (v7_struct_0 @ sk_A)
% 0.37/0.56         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.37/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.56               (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['92', '93'])).
% 0.37/0.56  thf('95', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf('96', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('97', plain,
% 0.37/0.56      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.37/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.56               (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.37/0.56  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('99', plain,
% 0.37/0.56      ((~ (v7_struct_0 @ sk_A))
% 0.37/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.56               (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('clc', [status(thm)], ['97', '98'])).
% 0.37/0.56  thf('100', plain,
% 0.37/0.56      (~
% 0.37/0.56       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.37/0.56         (u1_struct_0 @ sk_A))) | 
% 0.37/0.56       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['91', '99'])).
% 0.37/0.56  thf('101', plain, ($false),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['1', '46', '47', '100'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
