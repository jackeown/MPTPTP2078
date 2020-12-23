%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O51oFAu8AU

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:04 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 365 expanded)
%              Number of leaves         :   38 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          : 1325 (4383 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ( v1_subset_1 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( X21
       != ( k6_domain_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( v1_zfmisc_1 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('10',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X28 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('16',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( r1_tarski @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','30'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X14: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ~ ( v7_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('33',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('36',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('46',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('47',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','40','47'])).

thf('49',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('50',plain,(
    ! [X13: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v7_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('51',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

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

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( v1_tex_2 @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v7_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc10_tex_2])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('66',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['63','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','73'])).

thf('75',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['56'])).

thf('76',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

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

thf('77',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( ( sk_C_1 @ X23 @ X24 )
        = ( u1_struct_0 @ X23 ) )
      | ( v1_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf('84',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( m1_subset_1 @ ( sk_C_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v1_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 = X26 )
      | ( v1_subset_1 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('92',plain,
    ( ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('94',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( v1_subset_1 @ ( sk_C_1 @ X23 @ X24 ) @ ( u1_struct_0 @ X24 ) )
      | ( v1_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('95',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf('98',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['92','100'])).

thf('102',plain,(
    ! [X14: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ~ ( v7_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('103',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('105',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('106',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X13: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v7_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('108',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('110',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['56'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('112',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X33 ) @ X32 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v7_struct_0 @ X33 )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('113',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('115',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['110','118'])).

thf('120',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','74','75','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O51oFAu8AU
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:33:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.55/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.73  % Solved by: fo/fo7.sh
% 0.55/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.73  % done 249 iterations in 0.246s
% 0.55/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.73  % SZS output start Refutation
% 0.55/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.73  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.55/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.73  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.55/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.73  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.55/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.55/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.73  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.55/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.73  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.55/0.73  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.55/0.73  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.55/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.73  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.55/0.73  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.55/0.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.55/0.73  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.55/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.55/0.73  thf(t20_tex_2, conjecture,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.73           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.55/0.73             ( v1_subset_1 @
% 0.55/0.73               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.55/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.73    (~( ![A:$i]:
% 0.55/0.73        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.73          ( ![B:$i]:
% 0.55/0.73            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.73              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.55/0.73                ( v1_subset_1 @
% 0.55/0.73                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.55/0.73                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.55/0.73    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.55/0.73  thf('0', plain,
% 0.55/0.73      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73           (u1_struct_0 @ sk_A))
% 0.55/0.73        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('1', plain,
% 0.55/0.73      (~
% 0.55/0.73       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73         (u1_struct_0 @ sk_A))) | 
% 0.55/0.73       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.55/0.73      inference('split', [status(esa)], ['0'])).
% 0.55/0.73  thf('2', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(dt_k6_domain_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.55/0.73       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.55/0.73  thf('3', plain,
% 0.55/0.73      (![X15 : $i, X16 : $i]:
% 0.55/0.73         ((v1_xboole_0 @ X15)
% 0.55/0.73          | ~ (m1_subset_1 @ X16 @ X15)
% 0.55/0.73          | (m1_subset_1 @ (k6_domain_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15)))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.55/0.73  thf('4', plain,
% 0.55/0.73      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.73        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.73  thf(d7_subset_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.73       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.55/0.73  thf('5', plain,
% 0.55/0.73      (![X26 : $i, X27 : $i]:
% 0.55/0.73         (((X27) = (X26))
% 0.55/0.73          | (v1_subset_1 @ X27 @ X26)
% 0.55/0.73          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.55/0.73      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.55/0.73  thf('6', plain,
% 0.55/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.73        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73           (u1_struct_0 @ sk_A))
% 0.55/0.73        | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) = (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['4', '5'])).
% 0.55/0.73  thf('7', plain,
% 0.55/0.73      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73           (u1_struct_0 @ sk_A)))
% 0.55/0.73         <= (~
% 0.55/0.73             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('split', [status(esa)], ['0'])).
% 0.55/0.73  thf('8', plain,
% 0.55/0.73      (((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) = (u1_struct_0 @ sk_A))
% 0.55/0.73         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.55/0.73         <= (~
% 0.55/0.73             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['6', '7'])).
% 0.55/0.73  thf(d1_tex_2, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.55/0.73       ( ( v1_zfmisc_1 @ A ) <=>
% 0.55/0.73         ( ?[B:$i]:
% 0.55/0.73           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.55/0.73  thf('9', plain,
% 0.55/0.73      (![X21 : $i, X22 : $i]:
% 0.55/0.73         (((X21) != (k6_domain_1 @ X21 @ X22))
% 0.55/0.73          | ~ (m1_subset_1 @ X22 @ X21)
% 0.55/0.73          | (v1_zfmisc_1 @ X21)
% 0.55/0.73          | (v1_xboole_0 @ X21))),
% 0.55/0.73      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.55/0.73  thf('10', plain,
% 0.55/0.73      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.55/0.73         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.73         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.73         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.55/0.73         | ~ (m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))
% 0.55/0.73         <= (~
% 0.55/0.73             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.55/0.73  thf('11', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('12', plain,
% 0.55/0.73      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.55/0.73         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.73         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.73         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.55/0.73         <= (~
% 0.55/0.73             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('demod', [status(thm)], ['10', '11'])).
% 0.55/0.73  thf('13', plain,
% 0.55/0.73      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.55/0.73         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.55/0.73         <= (~
% 0.55/0.73             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('simplify', [status(thm)], ['12'])).
% 0.55/0.73  thf('14', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(dt_k1_tex_2, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.55/0.73         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.73       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.55/0.73         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.55/0.73         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.55/0.73  thf('15', plain,
% 0.55/0.73      (![X28 : $i, X29 : $i]:
% 0.55/0.73         (~ (l1_pre_topc @ X28)
% 0.55/0.73          | (v2_struct_0 @ X28)
% 0.55/0.73          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.55/0.73          | (m1_pre_topc @ (k1_tex_2 @ X28 @ X29) @ X28))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.55/0.73  thf('16', plain,
% 0.55/0.73      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.55/0.73        | (v2_struct_0 @ sk_A)
% 0.55/0.73        | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['14', '15'])).
% 0.55/0.73  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('18', plain,
% 0.55/0.73      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.55/0.73        | (v2_struct_0 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['16', '17'])).
% 0.55/0.73  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('20', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.55/0.73      inference('clc', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf(t35_borsuk_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( l1_pre_topc @ A ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_pre_topc @ B @ A ) =>
% 0.55/0.73           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.55/0.73  thf('21', plain,
% 0.55/0.73      (![X17 : $i, X18 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X17 @ X18)
% 0.55/0.73          | (r1_tarski @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18))
% 0.55/0.73          | ~ (l1_pre_topc @ X18))),
% 0.55/0.73      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.55/0.73  thf('22', plain,
% 0.55/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.73        | (r1_tarski @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.55/0.73           (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.55/0.73  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('24', plain,
% 0.55/0.73      ((r1_tarski @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.55/0.73        (u1_struct_0 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['22', '23'])).
% 0.55/0.73  thf(d3_tarski, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( r1_tarski @ A @ B ) <=>
% 0.55/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.55/0.73  thf('25', plain,
% 0.55/0.73      (![X4 : $i, X6 : $i]:
% 0.55/0.73         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.55/0.73  thf(d1_xboole_0, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.55/0.73  thf('26', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.55/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.55/0.73  thf('27', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.55/0.73  thf(d10_xboole_0, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.73  thf('28', plain,
% 0.55/0.73      (![X7 : $i, X9 : $i]:
% 0.55/0.73         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.55/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.73  thf('29', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['27', '28'])).
% 0.55/0.73  thf('30', plain,
% 0.55/0.73      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A))
% 0.55/0.73        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['24', '29'])).
% 0.55/0.73  thf('31', plain,
% 0.55/0.73      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.55/0.73         | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A))))
% 0.55/0.73         <= (~
% 0.55/0.73             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['13', '30'])).
% 0.55/0.73  thf(fc7_struct_0, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.55/0.73       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.55/0.73  thf('32', plain,
% 0.55/0.73      (![X14 : $i]:
% 0.55/0.73         ((v1_zfmisc_1 @ (u1_struct_0 @ X14))
% 0.55/0.73          | ~ (l1_struct_0 @ X14)
% 0.55/0.73          | ~ (v7_struct_0 @ X14))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.55/0.73  thf('33', plain,
% 0.55/0.73      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.55/0.73         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.55/0.73         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.55/0.73         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))
% 0.55/0.73         <= (~
% 0.55/0.73             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('sup+', [status(thm)], ['31', '32'])).
% 0.55/0.73  thf('34', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(fc2_tex_2, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.55/0.73         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.73       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.55/0.73         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.55/0.73         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.55/0.73  thf('35', plain,
% 0.55/0.73      (![X30 : $i, X31 : $i]:
% 0.55/0.73         (~ (l1_pre_topc @ X30)
% 0.55/0.73          | (v2_struct_0 @ X30)
% 0.55/0.73          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.55/0.73          | (v7_struct_0 @ (k1_tex_2 @ X30 @ X31)))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.55/0.73  thf('36', plain,
% 0.55/0.73      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.55/0.73        | (v2_struct_0 @ sk_A)
% 0.55/0.73        | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['34', '35'])).
% 0.55/0.73  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('38', plain,
% 0.55/0.73      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['36', '37'])).
% 0.55/0.73  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('40', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.55/0.73      inference('clc', [status(thm)], ['38', '39'])).
% 0.55/0.73  thf('41', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.55/0.73      inference('clc', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf(dt_m1_pre_topc, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( l1_pre_topc @ A ) =>
% 0.55/0.73       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.55/0.73  thf('42', plain,
% 0.55/0.73      (![X11 : $i, X12 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X11 @ X12)
% 0.55/0.73          | (l1_pre_topc @ X11)
% 0.55/0.73          | ~ (l1_pre_topc @ X12))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.55/0.73  thf('43', plain,
% 0.55/0.73      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['41', '42'])).
% 0.55/0.73  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('45', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.55/0.73      inference('demod', [status(thm)], ['43', '44'])).
% 0.55/0.73  thf(dt_l1_pre_topc, axiom,
% 0.55/0.73    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.55/0.73  thf('46', plain,
% 0.55/0.73      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.55/0.73  thf('47', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.55/0.73      inference('sup-', [status(thm)], ['45', '46'])).
% 0.55/0.73  thf('48', plain,
% 0.55/0.73      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.55/0.73         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.55/0.73         <= (~
% 0.55/0.73             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('demod', [status(thm)], ['33', '40', '47'])).
% 0.55/0.73  thf('49', plain,
% 0.55/0.73      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.73         <= (~
% 0.55/0.73             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('simplify', [status(thm)], ['48'])).
% 0.55/0.73  thf(fc6_struct_0, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.55/0.73       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.55/0.73  thf('50', plain,
% 0.55/0.73      (![X13 : $i]:
% 0.55/0.73         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X13))
% 0.55/0.73          | ~ (l1_struct_0 @ X13)
% 0.55/0.73          | (v7_struct_0 @ X13))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.55/0.73  thf('51', plain,
% 0.55/0.73      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.55/0.73         <= (~
% 0.55/0.73             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['49', '50'])).
% 0.55/0.73  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('53', plain,
% 0.55/0.73      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.55/0.73  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.73      inference('sup-', [status(thm)], ['52', '53'])).
% 0.55/0.73  thf('55', plain,
% 0.55/0.73      (((v7_struct_0 @ sk_A))
% 0.55/0.73         <= (~
% 0.55/0.73             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('demod', [status(thm)], ['51', '54'])).
% 0.55/0.73  thf('56', plain,
% 0.55/0.73      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73         (u1_struct_0 @ sk_A))
% 0.55/0.73        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('57', plain,
% 0.55/0.73      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))
% 0.55/0.73         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('split', [status(esa)], ['56'])).
% 0.55/0.73  thf('58', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.55/0.73      inference('clc', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf(cc10_tex_2, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_pre_topc @ B @ A ) =>
% 0.55/0.73           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.55/0.73             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.55/0.73  thf('59', plain,
% 0.55/0.73      (![X19 : $i, X20 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X19 @ X20)
% 0.55/0.73          | ~ (v1_tex_2 @ X19 @ X20)
% 0.55/0.73          | (v2_struct_0 @ X19)
% 0.55/0.73          | ~ (l1_pre_topc @ X20)
% 0.55/0.73          | ~ (v7_struct_0 @ X20)
% 0.55/0.73          | (v2_struct_0 @ X20))),
% 0.55/0.73      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.55/0.73  thf('60', plain,
% 0.55/0.73      (((v2_struct_0 @ sk_A)
% 0.55/0.73        | ~ (v7_struct_0 @ sk_A)
% 0.55/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.55/0.73        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.55/0.73        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['58', '59'])).
% 0.55/0.73  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('62', plain,
% 0.55/0.73      (((v2_struct_0 @ sk_A)
% 0.55/0.73        | ~ (v7_struct_0 @ sk_A)
% 0.55/0.73        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.55/0.73        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['60', '61'])).
% 0.55/0.73  thf('63', plain,
% 0.55/0.73      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.55/0.73         | ~ (v7_struct_0 @ sk_A)
% 0.55/0.73         | (v2_struct_0 @ sk_A)))
% 0.55/0.73         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['57', '62'])).
% 0.55/0.73  thf('64', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('65', plain,
% 0.55/0.73      (![X28 : $i, X29 : $i]:
% 0.55/0.73         (~ (l1_pre_topc @ X28)
% 0.55/0.73          | (v2_struct_0 @ X28)
% 0.55/0.73          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.55/0.73          | ~ (v2_struct_0 @ (k1_tex_2 @ X28 @ X29)))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.55/0.73  thf('66', plain,
% 0.55/0.73      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.55/0.73        | (v2_struct_0 @ sk_A)
% 0.55/0.73        | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['64', '65'])).
% 0.55/0.73  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('68', plain,
% 0.55/0.73      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['66', '67'])).
% 0.55/0.73  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('70', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.55/0.73      inference('clc', [status(thm)], ['68', '69'])).
% 0.55/0.73  thf('71', plain,
% 0.55/0.73      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.55/0.73         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('clc', [status(thm)], ['63', '70'])).
% 0.55/0.73  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('73', plain,
% 0.55/0.73      ((~ (v7_struct_0 @ sk_A))
% 0.55/0.73         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('clc', [status(thm)], ['71', '72'])).
% 0.55/0.73  thf('74', plain,
% 0.55/0.73      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73         (u1_struct_0 @ sk_A))) | 
% 0.55/0.73       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['55', '73'])).
% 0.55/0.73  thf('75', plain,
% 0.55/0.73      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73         (u1_struct_0 @ sk_A))) | 
% 0.55/0.73       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.55/0.73      inference('split', [status(esa)], ['56'])).
% 0.55/0.73  thf('76', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.55/0.73      inference('clc', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf(d3_tex_2, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( l1_pre_topc @ A ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_pre_topc @ B @ A ) =>
% 0.55/0.73           ( ( v1_tex_2 @ B @ A ) <=>
% 0.55/0.73             ( ![C:$i]:
% 0.55/0.73               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.73                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.55/0.73                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf('77', plain,
% 0.55/0.73      (![X23 : $i, X24 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X23 @ X24)
% 0.55/0.73          | ((sk_C_1 @ X23 @ X24) = (u1_struct_0 @ X23))
% 0.55/0.73          | (v1_tex_2 @ X23 @ X24)
% 0.55/0.73          | ~ (l1_pre_topc @ X24))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.55/0.73  thf('78', plain,
% 0.55/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.73        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.55/0.73        | ((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.55/0.73            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['76', '77'])).
% 0.55/0.73  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('80', plain,
% 0.55/0.73      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.55/0.73        | ((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.55/0.73            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))),
% 0.55/0.73      inference('demod', [status(thm)], ['78', '79'])).
% 0.55/0.73  thf('81', plain,
% 0.55/0.73      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('split', [status(esa)], ['0'])).
% 0.55/0.73  thf('82', plain,
% 0.55/0.73      ((((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.55/0.73          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['80', '81'])).
% 0.55/0.73  thf('83', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.55/0.73      inference('clc', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf('84', plain,
% 0.55/0.73      (![X23 : $i, X24 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X23 @ X24)
% 0.55/0.73          | (m1_subset_1 @ (sk_C_1 @ X23 @ X24) @ 
% 0.55/0.73             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.55/0.73          | (v1_tex_2 @ X23 @ X24)
% 0.55/0.73          | ~ (l1_pre_topc @ X24))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.55/0.73  thf('85', plain,
% 0.55/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.73        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.55/0.73        | (m1_subset_1 @ (sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A) @ 
% 0.55/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['83', '84'])).
% 0.55/0.73  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('87', plain,
% 0.55/0.73      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.55/0.73        | (m1_subset_1 @ (sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A) @ 
% 0.55/0.73           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('demod', [status(thm)], ['85', '86'])).
% 0.55/0.73  thf('88', plain,
% 0.55/0.73      ((((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.55/0.73          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.73         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('sup+', [status(thm)], ['82', '87'])).
% 0.55/0.73  thf('89', plain,
% 0.55/0.73      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('split', [status(esa)], ['0'])).
% 0.55/0.73  thf('90', plain,
% 0.55/0.73      (((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.55/0.73         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('clc', [status(thm)], ['88', '89'])).
% 0.55/0.73  thf('91', plain,
% 0.55/0.73      (![X26 : $i, X27 : $i]:
% 0.55/0.73         (((X27) = (X26))
% 0.55/0.73          | (v1_subset_1 @ X27 @ X26)
% 0.55/0.73          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.55/0.73      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.55/0.73  thf('92', plain,
% 0.55/0.73      ((((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.55/0.73          (u1_struct_0 @ sk_A))
% 0.55/0.73         | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A))))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['90', '91'])).
% 0.55/0.73  thf('93', plain,
% 0.55/0.73      ((((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.55/0.73          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['80', '81'])).
% 0.55/0.73  thf('94', plain,
% 0.55/0.73      (![X23 : $i, X24 : $i]:
% 0.55/0.73         (~ (m1_pre_topc @ X23 @ X24)
% 0.55/0.73          | ~ (v1_subset_1 @ (sk_C_1 @ X23 @ X24) @ (u1_struct_0 @ X24))
% 0.55/0.73          | (v1_tex_2 @ X23 @ X24)
% 0.55/0.73          | ~ (l1_pre_topc @ X24))),
% 0.55/0.73      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.55/0.73  thf('95', plain,
% 0.55/0.73      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.55/0.73            (u1_struct_0 @ sk_A))
% 0.55/0.73         | ~ (l1_pre_topc @ sk_A)
% 0.55/0.73         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.55/0.73         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['93', '94'])).
% 0.55/0.73  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('97', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.55/0.73      inference('clc', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf('98', plain,
% 0.55/0.73      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.55/0.73            (u1_struct_0 @ sk_A))
% 0.55/0.73         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.55/0.73  thf('99', plain,
% 0.55/0.73      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('split', [status(esa)], ['0'])).
% 0.55/0.73  thf('100', plain,
% 0.55/0.73      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.55/0.73           (u1_struct_0 @ sk_A)))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('clc', [status(thm)], ['98', '99'])).
% 0.55/0.73  thf('101', plain,
% 0.55/0.73      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A)))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('clc', [status(thm)], ['92', '100'])).
% 0.55/0.73  thf('102', plain,
% 0.55/0.73      (![X14 : $i]:
% 0.55/0.73         ((v1_zfmisc_1 @ (u1_struct_0 @ X14))
% 0.55/0.73          | ~ (l1_struct_0 @ X14)
% 0.55/0.73          | ~ (v7_struct_0 @ X14))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.55/0.73  thf('103', plain,
% 0.55/0.73      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.55/0.73         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.55/0.73         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('sup+', [status(thm)], ['101', '102'])).
% 0.55/0.73  thf('104', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.55/0.73      inference('clc', [status(thm)], ['38', '39'])).
% 0.55/0.73  thf('105', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.55/0.73      inference('sup-', [status(thm)], ['45', '46'])).
% 0.55/0.73  thf('106', plain,
% 0.55/0.73      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.55/0.73  thf('107', plain,
% 0.55/0.73      (![X13 : $i]:
% 0.55/0.73         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X13))
% 0.55/0.73          | ~ (l1_struct_0 @ X13)
% 0.55/0.73          | (v7_struct_0 @ X13))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.55/0.73  thf('108', plain,
% 0.55/0.73      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['106', '107'])).
% 0.55/0.73  thf('109', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.73      inference('sup-', [status(thm)], ['52', '53'])).
% 0.55/0.73  thf('110', plain,
% 0.55/0.73      (((v7_struct_0 @ sk_A))
% 0.55/0.73         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.55/0.73      inference('demod', [status(thm)], ['108', '109'])).
% 0.55/0.73  thf('111', plain,
% 0.55/0.73      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73         (u1_struct_0 @ sk_A)))
% 0.55/0.73         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('split', [status(esa)], ['56'])).
% 0.55/0.73  thf(t8_tex_2, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.73           ( ~( ( v1_subset_1 @
% 0.55/0.73                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.55/0.73                  ( u1_struct_0 @ A ) ) & 
% 0.55/0.73                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.55/0.73  thf('112', plain,
% 0.55/0.73      (![X32 : $i, X33 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X33))
% 0.55/0.73          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X33) @ X32) @ 
% 0.55/0.73               (u1_struct_0 @ X33))
% 0.55/0.73          | ~ (v7_struct_0 @ X33)
% 0.55/0.73          | ~ (l1_struct_0 @ X33)
% 0.55/0.73          | (v2_struct_0 @ X33))),
% 0.55/0.73      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.55/0.73  thf('113', plain,
% 0.55/0.73      ((((v2_struct_0 @ sk_A)
% 0.55/0.73         | ~ (l1_struct_0 @ sk_A)
% 0.55/0.73         | ~ (v7_struct_0 @ sk_A)
% 0.55/0.73         | ~ (m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))
% 0.55/0.73         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['111', '112'])).
% 0.55/0.73  thf('114', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.73      inference('sup-', [status(thm)], ['52', '53'])).
% 0.55/0.73  thf('115', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('116', plain,
% 0.55/0.73      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.55/0.73         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.55/0.73  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('118', plain,
% 0.55/0.73      ((~ (v7_struct_0 @ sk_A))
% 0.55/0.73         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73               (u1_struct_0 @ sk_A))))),
% 0.55/0.73      inference('clc', [status(thm)], ['116', '117'])).
% 0.55/0.73  thf('119', plain,
% 0.55/0.73      (~
% 0.55/0.73       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.55/0.73         (u1_struct_0 @ sk_A))) | 
% 0.55/0.73       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['110', '118'])).
% 0.55/0.73  thf('120', plain, ($false),
% 0.55/0.73      inference('sat_resolution*', [status(thm)], ['1', '74', '75', '119'])).
% 0.55/0.73  
% 0.55/0.73  % SZS output end Refutation
% 0.55/0.73  
% 0.55/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
