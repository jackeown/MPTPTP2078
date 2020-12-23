%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MItkgen8uV

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 309 expanded)
%              Number of leaves         :   32 (  97 expanded)
%              Depth                    :   19
%              Number of atoms          : 1271 (3801 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

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

thf(rc5_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ? [B: $i] :
          ( ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
          & ~ ( v1_zfmisc_1 @ B )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v7_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc5_tex_2])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 = X11 )
      | ( v1_subset_1 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_B @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X17: $i] :
      ( ~ ( v1_subset_1 @ ( sk_B @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v7_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc5_tex_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( sk_B @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X21 @ X20 ) @ X21 )
      | ( v1_zfmisc_1 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( v1_zfmisc_1 @ ( sk_B @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('15',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( v1_zfmisc_1 @ ( sk_B @ sk_A ) )
      | ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('19',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('21',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( v1_zfmisc_1 @ ( sk_B @ sk_A ) )
      | ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ ( sk_B @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X17: $i] :
      ( ~ ( v1_zfmisc_1 @ ( sk_B @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v7_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc5_tex_2])).

thf('26',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('28',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('36',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['38','39'])).

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

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ~ ( v1_tex_2 @ X6 @ X7 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v7_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc10_tex_2])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('48',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['45','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','55'])).

thf('57',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('58',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['38','39'])).

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

thf('59',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( ( sk_C @ X8 @ X9 )
        = ( u1_struct_0 @ X8 ) )
      | ( v1_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['38','39'])).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_subset_1 @ ( sk_C @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('71',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 = X11 )
      | ( v1_subset_1 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('74',plain,
    ( ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( v1_subset_1 @ ( sk_C @ X8 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ( v1_tex_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('77',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['38','39'])).

thf('80',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('84',plain,(
    ! [X5: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ~ ( v7_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('85',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
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

thf('87',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('88',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['38','39'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('94',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('99',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['85','92','99'])).

thf('101',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['32'])).

thf(t6_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf('102',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ X19 )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ X19 @ X18 ) @ X19 )
      | ~ ( v1_zfmisc_1 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t6_tex_2])).

thf('103',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('108',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','56','57','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MItkgen8uV
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 113 iterations in 0.039s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.20/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.20/0.48  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.20/0.48  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.48  thf(t20_tex_2, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.20/0.48             ( v1_subset_1 @
% 0.20/0.48               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.20/0.48                ( v1_subset_1 @
% 0.20/0.48                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.48                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48           (u1_struct_0 @ sk_A))
% 0.20/0.48        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (~
% 0.20/0.48       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48         (u1_struct_0 @ sk_A))) | 
% 0.20/0.48       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf(rc5_tex_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( ~( v7_struct_0 @ A ) ) & 
% 0.20/0.48         ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ?[B:$i]:
% 0.20/0.48         ( ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.48           ( ~( v1_zfmisc_1 @ B ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.48           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X17 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (sk_B @ X17) @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.48          | ~ (l1_struct_0 @ X17)
% 0.20/0.48          | (v7_struct_0 @ X17)
% 0.20/0.48          | (v2_struct_0 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [rc5_tex_2])).
% 0.20/0.48  thf(d7_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (((X12) = (X11))
% 0.20/0.48          | (v1_subset_1 @ X12 @ X11)
% 0.20/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | (v7_struct_0 @ X0)
% 0.20/0.48          | ~ (l1_struct_0 @ X0)
% 0.20/0.48          | (v1_subset_1 @ (sk_B @ X0) @ (u1_struct_0 @ X0))
% 0.20/0.48          | ((sk_B @ X0) = (u1_struct_0 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X17 : $i]:
% 0.20/0.48         (~ (v1_subset_1 @ (sk_B @ X17) @ (u1_struct_0 @ X17))
% 0.20/0.48          | ~ (l1_struct_0 @ X17)
% 0.20/0.48          | (v7_struct_0 @ X17)
% 0.20/0.48          | (v2_struct_0 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [rc5_tex_2])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_B @ X0) = (u1_struct_0 @ X0))
% 0.20/0.48          | ~ (l1_struct_0 @ X0)
% 0.20/0.48          | (v7_struct_0 @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | (v2_struct_0 @ X0)
% 0.20/0.48          | (v7_struct_0 @ X0)
% 0.20/0.48          | ~ (l1_struct_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | (v7_struct_0 @ X0)
% 0.20/0.48          | ~ (l1_struct_0 @ X0)
% 0.20/0.48          | ((sk_B @ X0) = (u1_struct_0 @ X0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.48  thf('8', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t7_tex_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.48           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X20 : $i, X21 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X20 @ X21)
% 0.20/0.48          | (v1_subset_1 @ (k6_domain_1 @ X21 @ X20) @ X21)
% 0.20/0.48          | (v1_zfmisc_1 @ X21)
% 0.20/0.48          | (v1_xboole_0 @ X21))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48           (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48           (u1_struct_0 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.48         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((((v1_zfmisc_1 @ (sk_B @ sk_A))
% 0.20/0.48         | ~ (l1_struct_0 @ sk_A)
% 0.20/0.48         | (v7_struct_0 @ sk_A)
% 0.20/0.48         | (v2_struct_0 @ sk_A)
% 0.20/0.48         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['7', '12'])).
% 0.20/0.48  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_l1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.48  thf('15', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.48  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((((v1_zfmisc_1 @ (sk_B @ sk_A))
% 0.20/0.48         | (v7_struct_0 @ sk_A)
% 0.20/0.48         | (v2_struct_0 @ sk_A)
% 0.20/0.48         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '16'])).
% 0.20/0.48  thf(fc2_struct_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X4 : $i]:
% 0.20/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.20/0.48          | ~ (l1_struct_0 @ X4)
% 0.20/0.48          | (v2_struct_0 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_A)
% 0.20/0.48         | (v7_struct_0 @ sk_A)
% 0.20/0.48         | (v1_zfmisc_1 @ (sk_B @ sk_A))
% 0.20/0.48         | (v2_struct_0 @ sk_A)
% 0.20/0.48         | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_A)
% 0.20/0.48         | (v7_struct_0 @ sk_A)
% 0.20/0.48         | (v1_zfmisc_1 @ (sk_B @ sk_A))
% 0.20/0.48         | (v2_struct_0 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((((v1_zfmisc_1 @ (sk_B @ sk_A))
% 0.20/0.48         | (v7_struct_0 @ sk_A)
% 0.20/0.48         | (v2_struct_0 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.48  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((((v7_struct_0 @ sk_A) | (v1_zfmisc_1 @ (sk_B @ sk_A))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X17 : $i]:
% 0.20/0.48         (~ (v1_zfmisc_1 @ (sk_B @ X17))
% 0.20/0.48          | ~ (l1_struct_0 @ X17)
% 0.20/0.48          | (v7_struct_0 @ X17)
% 0.20/0.48          | (v2_struct_0 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [rc5_tex_2])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((((v7_struct_0 @ sk_A)
% 0.20/0.48         | (v2_struct_0 @ sk_A)
% 0.20/0.48         | (v7_struct_0 @ sk_A)
% 0.20/0.48         | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      ((((v7_struct_0 @ sk_A) | (v2_struct_0 @ sk_A) | (v7_struct_0 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ sk_A)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.48  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (((v7_struct_0 @ sk_A))
% 0.20/0.48         <= (~
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48         (u1_struct_0 @ sk_A))
% 0.20/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.20/0.48         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['32'])).
% 0.20/0.48  thf('34', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k1_tex_2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.20/0.48         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.48         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X13)
% 0.20/0.48          | (v2_struct_0 @ X13)
% 0.20/0.48          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.20/0.48          | (m1_pre_topc @ (k1_tex_2 @ X13 @ X14) @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('40', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf(cc10_tex_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.48           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.20/0.48             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X6 @ X7)
% 0.20/0.48          | ~ (v1_tex_2 @ X6 @ X7)
% 0.20/0.48          | (v2_struct_0 @ X6)
% 0.20/0.48          | ~ (l1_pre_topc @ X7)
% 0.20/0.48          | ~ (v7_struct_0 @ X7)
% 0.20/0.48          | (v2_struct_0 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v7_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.20/0.48        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.48  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v7_struct_0 @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.20/0.48        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.20/0.48         | ~ (v7_struct_0 @ sk_A)
% 0.20/0.48         | (v2_struct_0 @ sk_A)))
% 0.20/0.48         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '44'])).
% 0.20/0.48  thf('46', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X13)
% 0.20/0.48          | (v2_struct_0 @ X13)
% 0.20/0.48          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.20/0.48          | ~ (v2_struct_0 @ (k1_tex_2 @ X13 @ X14)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.48  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.48  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('52', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.20/0.48      inference('clc', [status(thm)], ['50', '51'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.20/0.48         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['45', '52'])).
% 0.20/0.48  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      ((~ (v7_struct_0 @ sk_A))
% 0.20/0.48         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48         (u1_struct_0 @ sk_A))) | 
% 0.20/0.48       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '55'])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48         (u1_struct_0 @ sk_A))) | 
% 0.20/0.48       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['32'])).
% 0.20/0.48  thf('58', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf(d3_tex_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.48           ( ( v1_tex_2 @ B @ A ) <=>
% 0.20/0.48             ( ![C:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.48                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('59', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.48          | ((sk_C @ X8 @ X9) = (u1_struct_0 @ X8))
% 0.20/0.48          | (v1_tex_2 @ X8 @ X9)
% 0.20/0.48          | ~ (l1_pre_topc @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.48        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.48            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.48  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.48        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.48            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.20/0.48      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.48          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.48  thf('65', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf('66', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.48          | (m1_subset_1 @ (sk_C @ X8 @ X9) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | (v1_tex_2 @ X8 @ X9)
% 0.20/0.48          | ~ (l1_pre_topc @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.48        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.48  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('69', plain,
% 0.20/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.48        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.48  thf('70', plain,
% 0.20/0.48      ((((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['64', '69'])).
% 0.20/0.48  thf('71', plain,
% 0.20/0.48      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('72', plain,
% 0.20/0.48      (((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['70', '71'])).
% 0.20/0.48  thf('73', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (((X12) = (X11))
% 0.20/0.48          | (v1_subset_1 @ X12 @ X11)
% 0.20/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.48  thf('74', plain,
% 0.20/0.48      ((((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.20/0.48          (u1_struct_0 @ sk_A))
% 0.20/0.48         | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.48  thf('75', plain,
% 0.20/0.48      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.48          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.48  thf('76', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.48          | ~ (v1_subset_1 @ (sk_C @ X8 @ X9) @ (u1_struct_0 @ X9))
% 0.20/0.48          | (v1_tex_2 @ X8 @ X9)
% 0.20/0.48          | ~ (l1_pre_topc @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.48  thf('77', plain,
% 0.20/0.48      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.20/0.48            (u1_struct_0 @ sk_A))
% 0.20/0.48         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.48         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.48  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('79', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf('80', plain,
% 0.20/0.48      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.20/0.48            (u1_struct_0 @ sk_A))
% 0.20/0.48         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.20/0.48  thf('81', plain,
% 0.20/0.48      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('82', plain,
% 0.20/0.48      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.20/0.48           (u1_struct_0 @ sk_A)))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['80', '81'])).
% 0.20/0.48  thf('83', plain,
% 0.20/0.48      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['74', '82'])).
% 0.20/0.48  thf(fc7_struct_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.48       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.48  thf('84', plain,
% 0.20/0.48      (![X5 : $i]:
% 0.20/0.48         ((v1_zfmisc_1 @ (u1_struct_0 @ X5))
% 0.20/0.48          | ~ (l1_struct_0 @ X5)
% 0.20/0.48          | ~ (v7_struct_0 @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.20/0.48  thf('85', plain,
% 0.20/0.48      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.48         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.20/0.48         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['83', '84'])).
% 0.20/0.48  thf('86', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(fc2_tex_2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.20/0.48         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.48         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.20/0.48  thf('87', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X15)
% 0.20/0.48          | (v2_struct_0 @ X15)
% 0.20/0.48          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.20/0.48          | (v7_struct_0 @ (k1_tex_2 @ X15 @ X16)))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.20/0.48  thf('88', plain,
% 0.20/0.48      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.48  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('90', plain,
% 0.20/0.48      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.48  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('92', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.20/0.48      inference('clc', [status(thm)], ['90', '91'])).
% 0.20/0.48  thf('93', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf(dt_m1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.48  thf('94', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.48  thf('95', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.48  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('97', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.20/0.48      inference('demod', [status(thm)], ['95', '96'])).
% 0.20/0.48  thf('98', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.48  thf('99', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['97', '98'])).
% 0.20/0.48  thf('100', plain,
% 0.20/0.48      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['85', '92', '99'])).
% 0.20/0.48  thf('101', plain,
% 0.20/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48         (u1_struct_0 @ sk_A)))
% 0.20/0.48         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['32'])).
% 0.20/0.48  thf(t6_tex_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.48           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.20/0.48                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('102', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X18 @ X19)
% 0.20/0.48          | ~ (v1_subset_1 @ (k6_domain_1 @ X19 @ X18) @ X19)
% 0.20/0.48          | ~ (v1_zfmisc_1 @ X19)
% 0.20/0.48          | (v1_xboole_0 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [t6_tex_2])).
% 0.20/0.48  thf('103', plain,
% 0.20/0.48      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.48         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.48  thf('104', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('105', plain,
% 0.20/0.48      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.48         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['103', '104'])).
% 0.20/0.48  thf('106', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['100', '105'])).
% 0.20/0.48  thf('107', plain,
% 0.20/0.48      (![X4 : $i]:
% 0.20/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.20/0.48          | ~ (l1_struct_0 @ X4)
% 0.20/0.48          | (v2_struct_0 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.48  thf('108', plain,
% 0.20/0.48      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.48  thf('109', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('110', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A))
% 0.20/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.20/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48               (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['108', '109'])).
% 0.20/0.48  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('112', plain,
% 0.20/0.48      (~
% 0.20/0.48       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.48         (u1_struct_0 @ sk_A))) | 
% 0.20/0.48       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['110', '111'])).
% 0.20/0.48  thf('113', plain, ($false),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['1', '56', '57', '112'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
