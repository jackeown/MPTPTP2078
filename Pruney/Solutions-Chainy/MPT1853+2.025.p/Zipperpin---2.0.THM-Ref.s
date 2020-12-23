%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gMFIYaRxMX

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 392 expanded)
%              Number of leaves         :   30 ( 119 expanded)
%              Depth                    :   17
%              Number of atoms          :  969 (4888 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ X19 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X19 @ X18 ) @ X19 )
      | ( v1_zfmisc_1 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v7_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('8',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('14',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('16',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X11 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('23',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['25','26'])).

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

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( v1_tex_2 @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v7_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc10_tex_2])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('35',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','42'])).

thf('44',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('45',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['19'])).

thf('46',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['25','26'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10 = X9 )
      | ( v1_subset_1 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('52',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t13_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                <=> ( v1_tex_2 @ B @ A ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( X17
       != ( u1_struct_0 @ X15 ) )
      | ~ ( v1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( v1_tex_2 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t13_tex_2])).

thf('55',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_tex_2 @ X15 @ X16 )
      | ~ ( v1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_pre_topc @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['25','26'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('63',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v7_struct_0 @ X21 )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('66',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['25','26'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('67',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('72',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('75',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','72','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','43','44','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gMFIYaRxMX
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:53:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 62 iterations in 0.032s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.21/0.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.49  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.49  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.21/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.49  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(t20_tex_2, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.21/0.49             ( v1_subset_1 @
% 0.21/0.49               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.21/0.49                ( v1_subset_1 @
% 0.21/0.49                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.49                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49           (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (u1_struct_0 @ sk_A))) | 
% 0.21/0.49       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t7_tex_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.49           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X18 @ X19)
% 0.21/0.49          | (v1_subset_1 @ (k6_domain_1 @ X19 @ X18) @ X19)
% 0.21/0.49          | (v1_zfmisc_1 @ X19)
% 0.21/0.49          | (v1_xboole_0 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49           (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49           (u1_struct_0 @ sk_A)))
% 0.21/0.49         <= (~
% 0.21/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.49         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.49         <= (~
% 0.21/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf(fc6_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X4))
% 0.21/0.49          | ~ (l1_struct_0 @ X4)
% 0.21/0.49          | (v7_struct_0 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49         | (v7_struct_0 @ sk_A)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.49         <= (~
% 0.21/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_l1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.49  thf('10', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v7_struct_0 @ sk_A)))
% 0.21/0.49         <= (~
% 0.21/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('demod', [status(thm)], ['8', '11'])).
% 0.21/0.49  thf(fc2_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X3 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 0.21/0.49          | ~ (l1_struct_0 @ X3)
% 0.21/0.49          | (v2_struct_0 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((((v7_struct_0 @ sk_A) | (v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.49         <= (~
% 0.21/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((((v7_struct_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.21/0.49         <= (~
% 0.21/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (((v7_struct_0 @ sk_A))
% 0.21/0.49         <= (~
% 0.21/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.21/0.49         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['19'])).
% 0.21/0.49  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k1_tex_2, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.21/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.21/0.49         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.21/0.49         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X11)
% 0.21/0.49          | (v2_struct_0 @ X11)
% 0.21/0.49          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.21/0.49          | (m1_pre_topc @ (k1_tex_2 @ X11 @ X12) @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf(cc10_tex_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.21/0.49             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X7 @ X8)
% 0.21/0.49          | ~ (v1_tex_2 @ X7 @ X8)
% 0.21/0.49          | (v2_struct_0 @ X7)
% 0.21/0.49          | ~ (l1_pre_topc @ X8)
% 0.21/0.49          | ~ (v7_struct_0 @ X8)
% 0.21/0.49          | (v2_struct_0 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v7_struct_0 @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v7_struct_0 @ sk_A)
% 0.21/0.49        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49         | ~ (v7_struct_0 @ sk_A)
% 0.21/0.49         | (v2_struct_0 @ sk_A)))
% 0.21/0.49         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '31'])).
% 0.21/0.49  thf('33', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X11)
% 0.21/0.49          | (v2_struct_0 @ X11)
% 0.21/0.49          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.21/0.49          | ~ (v2_struct_0 @ (k1_tex_2 @ X11 @ X12)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.49  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.49  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('39', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.21/0.49         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('clc', [status(thm)], ['32', '39'])).
% 0.21/0.49  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      ((~ (v7_struct_0 @ sk_A))
% 0.21/0.49         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (u1_struct_0 @ sk_A))) | 
% 0.21/0.49       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (u1_struct_0 @ sk_A))) | 
% 0.21/0.49       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('split', [status(esa)], ['19'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (u1_struct_0 @ sk_A)))
% 0.21/0.49         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('split', [status(esa)], ['19'])).
% 0.21/0.49  thf('46', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf(t1_tsep_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( m1_subset_1 @
% 0.21/0.49             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X5 @ X6)
% 0.21/0.49          | (m1_subset_1 @ (u1_struct_0 @ X5) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.49          | ~ (l1_pre_topc @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.21/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf(d7_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         (((X10) = (X9))
% 0.21/0.49          | (v1_subset_1 @ X10 @ X9)
% 0.21/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.21/0.49         (u1_struct_0 @ sk_A))
% 0.21/0.49        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf(t13_tex_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.49                 ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) <=>
% 0.21/0.49                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.49          | ((X17) != (u1_struct_0 @ X15))
% 0.21/0.49          | ~ (v1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.21/0.49          | (v1_tex_2 @ X15 @ X16)
% 0.21/0.49          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.49          | ~ (l1_pre_topc @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t13_tex_2])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X16)
% 0.21/0.49          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.21/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.49          | (v1_tex_2 @ X15 @ X16)
% 0.21/0.49          | ~ (v1_subset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.21/0.49          | ~ (m1_pre_topc @ X15 @ X16))),
% 0.21/0.49      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      ((~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49        | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.21/0.49             (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['53', '55'])).
% 0.21/0.49  thf('57', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.21/0.49           (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['52', '59'])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.49  thf(t8_tex_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49           ( ~( ( v1_subset_1 @
% 0.21/0.49                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.49                  ( u1_struct_0 @ A ) ) & 
% 0.21/0.49                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      (![X20 : $i, X21 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.21/0.49          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X21) @ X20) @ 
% 0.21/0.49               (u1_struct_0 @ X21))
% 0.21/0.49          | ~ (v7_struct_0 @ X21)
% 0.21/0.49          | ~ (l1_struct_0 @ X21)
% 0.21/0.49          | (v2_struct_0 @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (~ (v1_subset_1 @ 
% 0.21/0.49              (k6_domain_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ X0) @ 
% 0.21/0.49              (u1_struct_0 @ sk_A))
% 0.21/0.49           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49           | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49           | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.49  thf('66', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf(dt_m1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X1 @ X2) | (l1_pre_topc @ X1) | ~ (l1_pre_topc @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.49  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('70', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['68', '69'])).
% 0.21/0.49  thf('71', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('72', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.49  thf('73', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(fc2_tex_2, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.21/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.21/0.49         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.21/0.49         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X13)
% 0.21/0.49          | (v2_struct_0 @ X13)
% 0.21/0.49          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.21/0.49          | (v7_struct_0 @ (k1_tex_2 @ X13 @ X14)))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.21/0.49  thf('75', plain,
% 0.21/0.49      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.49  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('77', plain,
% 0.21/0.49      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['75', '76'])).
% 0.21/0.49  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('79', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['77', '78'])).
% 0.21/0.49  thf('80', plain,
% 0.21/0.49      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.49  thf('81', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.21/0.49              (u1_struct_0 @ sk_A))
% 0.21/0.49           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['64', '65', '72', '79', '80'])).
% 0.21/0.49  thf('82', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('83', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49           | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.21/0.49                (u1_struct_0 @ sk_A))))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('clc', [status(thm)], ['81', '82'])).
% 0.21/0.49  thf('84', plain,
% 0.21/0.49      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) & 
% 0.21/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['45', '83'])).
% 0.21/0.49  thf('85', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('86', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (u1_struct_0 @ sk_A))) | 
% 0.21/0.49       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['84', '85'])).
% 0.21/0.49  thf('87', plain, ($false),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['1', '43', '44', '86'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
