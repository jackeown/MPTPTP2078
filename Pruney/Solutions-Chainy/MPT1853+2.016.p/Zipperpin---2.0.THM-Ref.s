%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zbnhS17TWS

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:04 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 333 expanded)
%              Number of leaves         :   35 ( 105 expanded)
%              Depth                    :   18
%              Number of atoms          : 1125 (3915 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X25 @ X24 ) @ X25 )
      | ( v1_zfmisc_1 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('7',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ~ ( v7_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(cc5_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_zfmisc_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_zfmisc_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_zfmisc_1 @ X6 )
      | ~ ( v1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_zfmisc_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_zfmisc_1 @ X0 )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('24',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('33',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','34'])).

thf('36',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['4','35'])).

thf('37',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('39',plain,(
    ! [X11: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 )
      | ( v7_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('40',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
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

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( v1_tex_2 @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v7_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc10_tex_2])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('55',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['52','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','62'])).

thf('64',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('65',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

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

thf('66',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( sk_C @ X15 @ X16 )
        = ( u1_struct_0 @ X15 ) )
      | ( v1_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf('73',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( sk_C @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('74',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf('78',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('80',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( v1_subset_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('81',plain,
    ( ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('83',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( v1_subset_1 @ ( sk_C @ X15 @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ( v1_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('84',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf('87',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['81','89'])).

thf('91',plain,(
    ! [X12: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ~ ( v7_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('92',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('94',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('95',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ! [X11: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 )
      | ( v7_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('97',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('99',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['45'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('101',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X27 ) @ X26 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v7_struct_0 @ X27 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['99','107'])).

thf('109',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','63','64','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zbnhS17TWS
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 238 iterations in 0.170s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.62  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.41/0.62  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.41/0.62  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.62  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.41/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.62  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.41/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(t20_tex_2, conjecture,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.62           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.41/0.62             ( v1_subset_1 @
% 0.41/0.62               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i]:
% 0.41/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.62          ( ![B:$i]:
% 0.41/0.62            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.62              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.41/0.62                ( v1_subset_1 @
% 0.41/0.62                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.41/0.62                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.62           (u1_struct_0 @ sk_A))
% 0.41/0.62        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      (~
% 0.41/0.62       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.62         (u1_struct_0 @ sk_A))) | 
% 0.41/0.62       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.41/0.62      inference('split', [status(esa)], ['0'])).
% 0.41/0.62  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t7_tex_2, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ B @ A ) =>
% 0.41/0.62           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X24 : $i, X25 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X24 @ X25)
% 0.41/0.62          | (v1_subset_1 @ (k6_domain_1 @ X25 @ X24) @ X25)
% 0.41/0.62          | (v1_zfmisc_1 @ X25)
% 0.41/0.62          | (v1_xboole_0 @ X25))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.41/0.62        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.62           (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.62  thf('5', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(fc2_tex_2, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.41/0.62         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.62       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.41/0.62         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.41/0.62         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      (![X22 : $i, X23 : $i]:
% 0.41/0.62         (~ (l1_pre_topc @ X22)
% 0.41/0.62          | (v2_struct_0 @ X22)
% 0.41/0.62          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.41/0.62          | (v7_struct_0 @ (k1_tex_2 @ X22 @ X23)))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.62  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.41/0.62  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('11', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.41/0.62      inference('clc', [status(thm)], ['9', '10'])).
% 0.41/0.62  thf(fc7_struct_0, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.62       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X12 : $i]:
% 0.41/0.62         ((v1_zfmisc_1 @ (u1_struct_0 @ X12))
% 0.41/0.62          | ~ (l1_struct_0 @ X12)
% 0.41/0.62          | ~ (v7_struct_0 @ X12))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.41/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.41/0.62  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.62  thf(t8_boole, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t8_boole])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.62  thf(t4_subset_1, axiom,
% 0.41/0.62    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.41/0.62  thf(cc5_funct_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( v1_zfmisc_1 @ A ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_zfmisc_1 @ B ) ) ) ))).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (![X6 : $i, X7 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.41/0.62          | (v1_zfmisc_1 @ X6)
% 0.41/0.62          | ~ (v1_zfmisc_1 @ X7))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc5_funct_1])).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ X1) | ~ (v1_zfmisc_1 @ X0) | (v1_zfmisc_1 @ X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (v7_struct_0 @ X0)
% 0.41/0.62          | ~ (l1_struct_0 @ X0)
% 0.41/0.62          | (v1_zfmisc_1 @ X1)
% 0.41/0.62          | ~ (v1_xboole_0 @ X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['12', '19'])).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ X0)
% 0.41/0.62          | (v1_zfmisc_1 @ X0)
% 0.41/0.62          | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['11', '20'])).
% 0.41/0.62  thf('22', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(dt_k1_tex_2, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.41/0.62         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.62       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.41/0.62         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.41/0.62         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      (![X20 : $i, X21 : $i]:
% 0.41/0.62         (~ (l1_pre_topc @ X20)
% 0.41/0.62          | (v2_struct_0 @ X20)
% 0.41/0.62          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.41/0.62          | (m1_pre_topc @ (k1_tex_2 @ X20 @ X21) @ X20))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.41/0.62        | (v2_struct_0 @ sk_A)
% 0.41/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.62  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.62  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('28', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.41/0.62      inference('clc', [status(thm)], ['26', '27'])).
% 0.41/0.62  thf(dt_m1_pre_topc, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( l1_pre_topc @ A ) =>
% 0.41/0.62       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      (![X9 : $i, X10 : $i]:
% 0.41/0.62         (~ (m1_pre_topc @ X9 @ X10)
% 0.41/0.62          | (l1_pre_topc @ X9)
% 0.41/0.62          | ~ (l1_pre_topc @ X10))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.62  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('32', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.62  thf(dt_l1_pre_topc, axiom,
% 0.41/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.62  thf('33', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.62  thf('34', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.63  thf('35', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_zfmisc_1 @ X0))),
% 0.41/0.63      inference('demod', [status(thm)], ['21', '34'])).
% 0.41/0.63  thf('36', plain,
% 0.41/0.63      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63         (u1_struct_0 @ sk_A))
% 0.41/0.63        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.63      inference('clc', [status(thm)], ['4', '35'])).
% 0.41/0.63  thf('37', plain,
% 0.41/0.63      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63           (u1_struct_0 @ sk_A)))
% 0.41/0.63         <= (~
% 0.41/0.63             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63               (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('split', [status(esa)], ['0'])).
% 0.41/0.63  thf('38', plain,
% 0.41/0.63      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.63         <= (~
% 0.41/0.63             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63               (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.63  thf(fc6_struct_0, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.63       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.63  thf('39', plain,
% 0.41/0.63      (![X11 : $i]:
% 0.41/0.63         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X11))
% 0.41/0.63          | ~ (l1_struct_0 @ X11)
% 0.41/0.63          | (v7_struct_0 @ X11))),
% 0.41/0.63      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.41/0.63  thf('40', plain,
% 0.41/0.63      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.41/0.63         <= (~
% 0.41/0.63             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63               (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.63  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('42', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.63  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.63  thf('44', plain,
% 0.41/0.63      (((v7_struct_0 @ sk_A))
% 0.41/0.63         <= (~
% 0.41/0.63             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63               (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('demod', [status(thm)], ['40', '43'])).
% 0.41/0.63  thf('45', plain,
% 0.41/0.63      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63         (u1_struct_0 @ sk_A))
% 0.41/0.63        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('46', plain,
% 0.41/0.63      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.41/0.63         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('split', [status(esa)], ['45'])).
% 0.41/0.63  thf('47', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.41/0.63      inference('clc', [status(thm)], ['26', '27'])).
% 0.41/0.63  thf(cc10_tex_2, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.63       ( ![B:$i]:
% 0.41/0.63         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.63           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.41/0.63             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.41/0.63  thf('48', plain,
% 0.41/0.63      (![X13 : $i, X14 : $i]:
% 0.41/0.63         (~ (m1_pre_topc @ X13 @ X14)
% 0.41/0.63          | ~ (v1_tex_2 @ X13 @ X14)
% 0.41/0.63          | (v2_struct_0 @ X13)
% 0.41/0.63          | ~ (l1_pre_topc @ X14)
% 0.41/0.63          | ~ (v7_struct_0 @ X14)
% 0.41/0.63          | (v2_struct_0 @ X14))),
% 0.41/0.63      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.41/0.63  thf('49', plain,
% 0.41/0.63      (((v2_struct_0 @ sk_A)
% 0.41/0.63        | ~ (v7_struct_0 @ sk_A)
% 0.41/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.41/0.63        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.41/0.63        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.41/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.41/0.63  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('51', plain,
% 0.41/0.63      (((v2_struct_0 @ sk_A)
% 0.41/0.63        | ~ (v7_struct_0 @ sk_A)
% 0.41/0.63        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.41/0.63        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.41/0.63      inference('demod', [status(thm)], ['49', '50'])).
% 0.41/0.63  thf('52', plain,
% 0.41/0.63      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.41/0.63         | ~ (v7_struct_0 @ sk_A)
% 0.41/0.63         | (v2_struct_0 @ sk_A)))
% 0.41/0.63         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['46', '51'])).
% 0.41/0.63  thf('53', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('54', plain,
% 0.41/0.63      (![X20 : $i, X21 : $i]:
% 0.41/0.63         (~ (l1_pre_topc @ X20)
% 0.41/0.63          | (v2_struct_0 @ X20)
% 0.41/0.63          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.41/0.63          | ~ (v2_struct_0 @ (k1_tex_2 @ X20 @ X21)))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.41/0.63  thf('55', plain,
% 0.41/0.63      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.41/0.63        | (v2_struct_0 @ sk_A)
% 0.41/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.63      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.63  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('57', plain,
% 0.41/0.63      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.41/0.63      inference('demod', [status(thm)], ['55', '56'])).
% 0.41/0.63  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('59', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.41/0.63      inference('clc', [status(thm)], ['57', '58'])).
% 0.41/0.63  thf('60', plain,
% 0.41/0.63      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.41/0.63         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('clc', [status(thm)], ['52', '59'])).
% 0.41/0.63  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('62', plain,
% 0.41/0.63      ((~ (v7_struct_0 @ sk_A))
% 0.41/0.63         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('clc', [status(thm)], ['60', '61'])).
% 0.41/0.63  thf('63', plain,
% 0.41/0.63      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63         (u1_struct_0 @ sk_A))) | 
% 0.41/0.63       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.41/0.63      inference('sup-', [status(thm)], ['44', '62'])).
% 0.41/0.63  thf('64', plain,
% 0.41/0.63      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63         (u1_struct_0 @ sk_A))) | 
% 0.41/0.63       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.41/0.63      inference('split', [status(esa)], ['45'])).
% 0.41/0.63  thf('65', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.41/0.63      inference('clc', [status(thm)], ['26', '27'])).
% 0.41/0.63  thf(d3_tex_2, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( l1_pre_topc @ A ) =>
% 0.41/0.63       ( ![B:$i]:
% 0.41/0.63         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.63           ( ( v1_tex_2 @ B @ A ) <=>
% 0.41/0.63             ( ![C:$i]:
% 0.41/0.63               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.63                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.41/0.63                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.41/0.63  thf('66', plain,
% 0.41/0.63      (![X15 : $i, X16 : $i]:
% 0.41/0.63         (~ (m1_pre_topc @ X15 @ X16)
% 0.41/0.63          | ((sk_C @ X15 @ X16) = (u1_struct_0 @ X15))
% 0.41/0.63          | (v1_tex_2 @ X15 @ X16)
% 0.41/0.63          | ~ (l1_pre_topc @ X16))),
% 0.41/0.63      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.41/0.63  thf('67', plain,
% 0.41/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.63        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.41/0.63        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.41/0.63            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['65', '66'])).
% 0.41/0.63  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('69', plain,
% 0.41/0.63      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.41/0.63        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.41/0.63            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.41/0.63      inference('demod', [status(thm)], ['67', '68'])).
% 0.41/0.63  thf('70', plain,
% 0.41/0.63      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('split', [status(esa)], ['0'])).
% 0.41/0.63  thf('71', plain,
% 0.41/0.63      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.41/0.63          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['69', '70'])).
% 0.41/0.63  thf('72', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.41/0.63      inference('clc', [status(thm)], ['26', '27'])).
% 0.41/0.63  thf('73', plain,
% 0.41/0.63      (![X15 : $i, X16 : $i]:
% 0.41/0.63         (~ (m1_pre_topc @ X15 @ X16)
% 0.41/0.63          | (m1_subset_1 @ (sk_C @ X15 @ X16) @ 
% 0.41/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.63          | (v1_tex_2 @ X15 @ X16)
% 0.41/0.63          | ~ (l1_pre_topc @ X16))),
% 0.41/0.63      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.41/0.63  thf('74', plain,
% 0.41/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.63        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.41/0.63        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) @ 
% 0.41/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['72', '73'])).
% 0.41/0.63  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('76', plain,
% 0.41/0.63      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.41/0.63        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) @ 
% 0.41/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('demod', [status(thm)], ['74', '75'])).
% 0.41/0.63  thf('77', plain,
% 0.41/0.63      ((((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.41/0.63          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.63         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('sup+', [status(thm)], ['71', '76'])).
% 0.41/0.63  thf('78', plain,
% 0.41/0.63      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('split', [status(esa)], ['0'])).
% 0.41/0.63  thf('79', plain,
% 0.41/0.63      (((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.41/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('clc', [status(thm)], ['77', '78'])).
% 0.41/0.63  thf(d7_subset_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.63       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.41/0.63  thf('80', plain,
% 0.41/0.63      (![X18 : $i, X19 : $i]:
% 0.41/0.63         (((X19) = (X18))
% 0.41/0.63          | (v1_subset_1 @ X19 @ X18)
% 0.41/0.63          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.41/0.63      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.41/0.63  thf('81', plain,
% 0.41/0.63      ((((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.41/0.63          (u1_struct_0 @ sk_A))
% 0.41/0.63         | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['79', '80'])).
% 0.41/0.63  thf('82', plain,
% 0.41/0.63      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.41/0.63          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['69', '70'])).
% 0.41/0.63  thf('83', plain,
% 0.41/0.63      (![X15 : $i, X16 : $i]:
% 0.41/0.63         (~ (m1_pre_topc @ X15 @ X16)
% 0.41/0.63          | ~ (v1_subset_1 @ (sk_C @ X15 @ X16) @ (u1_struct_0 @ X16))
% 0.41/0.63          | (v1_tex_2 @ X15 @ X16)
% 0.41/0.63          | ~ (l1_pre_topc @ X16))),
% 0.41/0.63      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.41/0.63  thf('84', plain,
% 0.41/0.63      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.41/0.63            (u1_struct_0 @ sk_A))
% 0.41/0.63         | ~ (l1_pre_topc @ sk_A)
% 0.41/0.63         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.41/0.63         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['82', '83'])).
% 0.41/0.63  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('86', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.41/0.63      inference('clc', [status(thm)], ['26', '27'])).
% 0.41/0.63  thf('87', plain,
% 0.41/0.63      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.41/0.63            (u1_struct_0 @ sk_A))
% 0.41/0.63         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.41/0.63  thf('88', plain,
% 0.41/0.63      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('split', [status(esa)], ['0'])).
% 0.41/0.63  thf('89', plain,
% 0.41/0.63      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.41/0.63           (u1_struct_0 @ sk_A)))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('clc', [status(thm)], ['87', '88'])).
% 0.41/0.63  thf('90', plain,
% 0.41/0.63      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('clc', [status(thm)], ['81', '89'])).
% 0.41/0.63  thf('91', plain,
% 0.41/0.63      (![X12 : $i]:
% 0.41/0.63         ((v1_zfmisc_1 @ (u1_struct_0 @ X12))
% 0.41/0.63          | ~ (l1_struct_0 @ X12)
% 0.41/0.63          | ~ (v7_struct_0 @ X12))),
% 0.41/0.63      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.41/0.63  thf('92', plain,
% 0.41/0.63      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.41/0.63         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.41/0.63         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('sup+', [status(thm)], ['90', '91'])).
% 0.41/0.63  thf('93', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.41/0.63      inference('clc', [status(thm)], ['9', '10'])).
% 0.41/0.63  thf('94', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.41/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.63  thf('95', plain,
% 0.41/0.63      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.41/0.63  thf('96', plain,
% 0.41/0.63      (![X11 : $i]:
% 0.41/0.63         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X11))
% 0.41/0.63          | ~ (l1_struct_0 @ X11)
% 0.41/0.63          | (v7_struct_0 @ X11))),
% 0.41/0.63      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.41/0.63  thf('97', plain,
% 0.41/0.63      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['95', '96'])).
% 0.41/0.63  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.63  thf('99', plain,
% 0.41/0.63      (((v7_struct_0 @ sk_A))
% 0.41/0.63         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.41/0.63      inference('demod', [status(thm)], ['97', '98'])).
% 0.41/0.63  thf('100', plain,
% 0.41/0.63      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63         (u1_struct_0 @ sk_A)))
% 0.41/0.63         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63               (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('split', [status(esa)], ['45'])).
% 0.41/0.63  thf(t8_tex_2, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.63       ( ![B:$i]:
% 0.41/0.63         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.63           ( ~( ( v1_subset_1 @
% 0.41/0.63                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.41/0.63                  ( u1_struct_0 @ A ) ) & 
% 0.41/0.63                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.41/0.63  thf('101', plain,
% 0.41/0.63      (![X26 : $i, X27 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.41/0.63          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X27) @ X26) @ 
% 0.41/0.63               (u1_struct_0 @ X27))
% 0.41/0.63          | ~ (v7_struct_0 @ X27)
% 0.41/0.63          | ~ (l1_struct_0 @ X27)
% 0.41/0.63          | (v2_struct_0 @ X27))),
% 0.41/0.63      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.41/0.63  thf('102', plain,
% 0.41/0.63      ((((v2_struct_0 @ sk_A)
% 0.41/0.63         | ~ (l1_struct_0 @ sk_A)
% 0.41/0.63         | ~ (v7_struct_0 @ sk_A)
% 0.41/0.63         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.41/0.63         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63               (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['100', '101'])).
% 0.41/0.63  thf('103', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.63  thf('104', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('105', plain,
% 0.41/0.63      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.41/0.63         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63               (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.41/0.63  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('107', plain,
% 0.41/0.63      ((~ (v7_struct_0 @ sk_A))
% 0.41/0.63         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63               (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('clc', [status(thm)], ['105', '106'])).
% 0.41/0.63  thf('108', plain,
% 0.41/0.63      (~
% 0.41/0.63       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.63         (u1_struct_0 @ sk_A))) | 
% 0.41/0.63       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.41/0.63      inference('sup-', [status(thm)], ['99', '107'])).
% 0.41/0.63  thf('109', plain, ($false),
% 0.41/0.63      inference('sat_resolution*', [status(thm)], ['1', '63', '64', '108'])).
% 0.41/0.63  
% 0.41/0.63  % SZS output end Refutation
% 0.41/0.63  
% 0.50/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
