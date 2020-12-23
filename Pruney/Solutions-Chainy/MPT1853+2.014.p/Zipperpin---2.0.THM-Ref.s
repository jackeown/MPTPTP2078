%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3puNNhTZ0P

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 330 expanded)
%              Number of leaves         :   33 ( 103 expanded)
%              Depth                    :   18
%              Number of atoms          : 1244 (4024 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( v1_subset_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( X13
       != ( k6_domain_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( v1_zfmisc_1 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
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

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v7_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('15',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('24',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

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

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( v1_tex_2 @ X15 @ X16 )
      | ( X17
       != ( u1_struct_0 @ X15 ) )
      | ( v1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_tex_2 @ X15 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','38'])).

thf('40',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_subset_1 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      & ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','43'])).

thf('45',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('46',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

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

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( v1_tex_2 @ X11 @ X12 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v7_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc10_tex_2])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('54',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['51','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','61'])).

thf('63',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('64',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('65',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( v1_subset_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('66',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf('68',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( sk_C @ X15 @ X16 )
        = ( u1_struct_0 @ X15 ) )
      | ( v1_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( v1_subset_1 @ ( sk_C @ X15 @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ( v1_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('75',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf('78',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['66','80'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('82',plain,(
    ! [X6: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ~ ( v7_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('83',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
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

thf('85',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('86',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('92',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('97',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['83','90','97'])).

thf('99',plain,(
    ! [X5: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v7_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('100',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('102',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('104',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ X24 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v7_struct_0 @ X25 )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('105',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('107',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['102','110'])).

thf('112',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','62','63','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3puNNhTZ0P
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 119 iterations in 0.084s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.54  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.21/0.54  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(t20_tex_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.21/0.54             ( v1_subset_1 @
% 0.21/0.54               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.21/0.54                ( v1_subset_1 @
% 0.21/0.54                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.54                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54           (u1_struct_0 @ sk_A))
% 0.21/0.54        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (~
% 0.21/0.54       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A))) | 
% 0.21/0.54       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k6_domain_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.54       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ X7)
% 0.21/0.54          | ~ (m1_subset_1 @ X8 @ X7)
% 0.21/0.54          | (m1_subset_1 @ (k6_domain_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf(d7_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X18 : $i, X19 : $i]:
% 0.21/0.54         (((X19) = (X18))
% 0.21/0.54          | (v1_subset_1 @ X19 @ X18)
% 0.21/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54           (u1_struct_0 @ sk_A))
% 0.21/0.54        | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54           (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf(d1_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54       ( ( v1_zfmisc_1 @ A ) <=>
% 0.21/0.54         ( ?[B:$i]:
% 0.21/0.54           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         (((X13) != (k6_domain_1 @ X13 @ X14))
% 0.21/0.54          | ~ (m1_subset_1 @ X14 @ X13)
% 0.21/0.54          | (v1_zfmisc_1 @ X13)
% 0.21/0.54          | (v1_xboole_0 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf('11', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.54  thf(fc6_struct_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.54       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X5 : $i]:
% 0.21/0.54         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X5))
% 0.21/0.54          | ~ (l1_struct_0 @ X5)
% 0.21/0.54          | (v7_struct_0 @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v7_struct_0 @ sk_A)
% 0.21/0.54         | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_l1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.54  thf('17', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.54  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v7_struct_0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.21/0.54         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['20'])).
% 0.21/0.54  thf('22', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k1_tex_2, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.21/0.54         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.21/0.54         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X20)
% 0.21/0.54          | (v2_struct_0 @ X20)
% 0.21/0.54          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.21/0.54          | (m1_pre_topc @ (k1_tex_2 @ X20 @ X21) @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('28', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf(t1_tsep_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.54           ( m1_subset_1 @
% 0.21/0.54             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.54          | (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.54          | ~ (l1_pre_topc @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.54  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.54  thf(d3_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.54           ( ( v1_tex_2 @ B @ A ) <=>
% 0.21/0.54             ( ![C:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.54                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.54          | ~ (v1_tex_2 @ X15 @ X16)
% 0.21/0.54          | ((X17) != (u1_struct_0 @ X15))
% 0.21/0.54          | (v1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.21/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.54          | ~ (l1_pre_topc @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X16)
% 0.21/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.21/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.54          | (v1_subset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.21/0.54          | ~ (v1_tex_2 @ X15 @ X16)
% 0.21/0.54          | ~ (m1_pre_topc @ X15 @ X16))),
% 0.21/0.54      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      ((~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54           (u1_struct_0 @ sk_A))
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['32', '34'])).
% 0.21/0.54  thf('36', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54           (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['21', '38'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.54  thf(cc4_subset_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.54          | ~ (v1_subset_1 @ X0 @ X1)
% 0.21/0.54          | ~ (v1_xboole_0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54             (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['39', '42'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (((v7_struct_0 @ sk_A))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))) & 
% 0.21/0.54             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['19', '43'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.21/0.54         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['20'])).
% 0.21/0.54  thf('46', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf(cc10_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.54           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.21/0.54             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.54          | ~ (v1_tex_2 @ X11 @ X12)
% 0.21/0.54          | (v2_struct_0 @ X11)
% 0.21/0.54          | ~ (l1_pre_topc @ X12)
% 0.21/0.54          | ~ (v7_struct_0 @ X12)
% 0.21/0.54          | (v2_struct_0 @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v7_struct_0 @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.54  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v7_struct_0 @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54         | ~ (v7_struct_0 @ sk_A)
% 0.21/0.54         | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['45', '50'])).
% 0.21/0.54  thf('52', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X20)
% 0.21/0.54          | (v2_struct_0 @ X20)
% 0.21/0.54          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.21/0.54          | ~ (v2_struct_0 @ (k1_tex_2 @ X20 @ X21)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.54  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.54  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('58', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.21/0.54         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['51', '58'])).
% 0.21/0.54  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      ((~ (v7_struct_0 @ sk_A))
% 0.21/0.54         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A))) | 
% 0.21/0.54       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '61'])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A))) | 
% 0.21/0.54       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.21/0.54      inference('split', [status(esa)], ['20'])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      (![X18 : $i, X19 : $i]:
% 0.21/0.54         (((X19) = (X18))
% 0.21/0.54          | (v1_subset_1 @ X19 @ X18)
% 0.21/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A))
% 0.21/0.54        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.54  thf('67', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.54          | ((sk_C @ X15 @ X16) = (u1_struct_0 @ X15))
% 0.21/0.54          | (v1_tex_2 @ X15 @ X16)
% 0.21/0.54          | ~ (l1_pre_topc @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.54  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('71', plain,
% 0.21/0.54      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.21/0.54      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.54          | ~ (v1_subset_1 @ (sk_C @ X15 @ X16) @ (u1_struct_0 @ X16))
% 0.21/0.54          | (v1_tex_2 @ X15 @ X16)
% 0.21/0.54          | ~ (l1_pre_topc @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.54  thf('75', plain,
% 0.21/0.54      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54            (u1_struct_0 @ sk_A))
% 0.21/0.54         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.54  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('77', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54            (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.21/0.54  thf('79', plain,
% 0.21/0.54      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('80', plain,
% 0.21/0.54      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54           (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['78', '79'])).
% 0.21/0.54  thf('81', plain,
% 0.21/0.54      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['66', '80'])).
% 0.21/0.54  thf(fc7_struct_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.54       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.54  thf('82', plain,
% 0.21/0.54      (![X6 : $i]:
% 0.21/0.54         ((v1_zfmisc_1 @ (u1_struct_0 @ X6))
% 0.21/0.54          | ~ (l1_struct_0 @ X6)
% 0.21/0.54          | ~ (v7_struct_0 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.21/0.54  thf('83', plain,
% 0.21/0.54      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['81', '82'])).
% 0.21/0.54  thf('84', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(fc2_tex_2, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.21/0.54         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.21/0.54         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.21/0.54  thf('85', plain,
% 0.21/0.54      (![X22 : $i, X23 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X22)
% 0.21/0.54          | (v2_struct_0 @ X22)
% 0.21/0.54          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.21/0.54          | (v7_struct_0 @ (k1_tex_2 @ X22 @ X23)))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.21/0.54  thf('86', plain,
% 0.21/0.54      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.54  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('88', plain,
% 0.21/0.54      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.54  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('90', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['88', '89'])).
% 0.21/0.54  thf('91', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf(dt_m1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.54  thf('92', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.54  thf('93', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.54  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('95', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['93', '94'])).
% 0.21/0.54  thf('96', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.54  thf('97', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.54  thf('98', plain,
% 0.21/0.54      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['83', '90', '97'])).
% 0.21/0.54  thf('99', plain,
% 0.21/0.54      (![X5 : $i]:
% 0.21/0.54         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X5))
% 0.21/0.54          | ~ (l1_struct_0 @ X5)
% 0.21/0.54          | (v7_struct_0 @ X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.21/0.54  thf('100', plain,
% 0.21/0.54      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['98', '99'])).
% 0.21/0.54  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('102', plain,
% 0.21/0.54      (((v7_struct_0 @ sk_A))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['100', '101'])).
% 0.21/0.54  thf('103', plain,
% 0.21/0.54      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('split', [status(esa)], ['20'])).
% 0.21/0.54  thf(t8_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54           ( ~( ( v1_subset_1 @
% 0.21/0.54                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.54                  ( u1_struct_0 @ A ) ) & 
% 0.21/0.54                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('104', plain,
% 0.21/0.54      (![X24 : $i, X25 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.21/0.54          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X25) @ X24) @ 
% 0.21/0.54               (u1_struct_0 @ X25))
% 0.21/0.54          | ~ (v7_struct_0 @ X25)
% 0.21/0.54          | ~ (l1_struct_0 @ X25)
% 0.21/0.54          | (v2_struct_0 @ X25))),
% 0.21/0.54      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.21/0.54  thf('105', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_A)
% 0.21/0.54         | ~ (l1_struct_0 @ sk_A)
% 0.21/0.54         | ~ (v7_struct_0 @ sk_A)
% 0.21/0.54         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['103', '104'])).
% 0.21/0.54  thf('106', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.54  thf('107', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('108', plain,
% 0.21/0.54      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.21/0.54         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.21/0.54  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('110', plain,
% 0.21/0.54      ((~ (v7_struct_0 @ sk_A))
% 0.21/0.54         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('clc', [status(thm)], ['108', '109'])).
% 0.21/0.54  thf('111', plain,
% 0.21/0.54      (~
% 0.21/0.54       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A))) | 
% 0.21/0.54       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['102', '110'])).
% 0.21/0.54  thf('112', plain, ($false),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['1', '62', '63', '111'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
