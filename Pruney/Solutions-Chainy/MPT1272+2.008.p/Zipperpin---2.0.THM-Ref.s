%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kntMNmNq47

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:29 EST 2020

% Result     : Theorem 2.60s
% Output     : Refutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  229 (2804 expanded)
%              Number of leaves         :   33 ( 848 expanded)
%              Depth                    :   31
%              Number of atoms          : 2011 (26193 expanded)
%              Number of equality atoms :   86 ( 960 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t91_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tops_1 @ B @ A )
             => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t91_tops_1])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('7',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('20',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','20'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('30',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','20'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k2_pre_topc @ X33 @ X32 )
       != ( k2_struct_0 @ X33 ) )
      | ( v1_tops_1 @ X32 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('41',plain,(
    ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('44',plain,(
    ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','44'])).

thf('46',plain,(
    ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','20'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('48',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X43 @ X42 ) @ X42 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('54',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('58',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r1_tarski @ X27 @ X29 )
      | ( r1_tarski @ ( k2_pre_topc @ X28 @ X27 ) @ ( k2_pre_topc @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t27_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('64',plain,(
    ! [X41: $i] :
      ( ( ( k2_pre_topc @ X41 @ ( k2_struct_0 @ X41 ) )
        = ( k2_struct_0 @ X41 ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_1])).

thf('65',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','80'])).

thf('82',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('87',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v1_tops_1 @ X32 @ X33 )
      | ( ( k2_pre_topc @ X33 @ X32 )
        = ( k2_struct_0 @ X33 ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('90',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('91',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k2_pre_topc @ X33 @ X32 )
       != ( k2_struct_0 @ X33 ) )
      | ( v1_tops_1 @ X32 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X41: $i] :
      ( ( ( k2_pre_topc @ X41 @ ( k2_struct_0 @ X41 ) )
        = ( k2_struct_0 @ X41 ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['88','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('99',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','104'])).

thf('106',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('118',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('119',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','20'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('123',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k1_tops_1 @ X31 @ X30 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_pre_topc @ X31 @ ( k3_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 ) ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('124',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('127',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('128',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('130',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('131',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('133',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['128','133'])).

thf('135',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['124','125','134'])).

thf('136',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('137',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('138',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('140',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('142',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('143',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('145',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X8 @ X9 )
        = ( k4_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('147',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','147'])).

thf('149',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('150',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['124','125','134'])).

thf('151',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('153',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('154',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','154'])).

thf('156',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v1_tops_1 @ X32 @ X33 )
      | ( ( k2_pre_topc @ X33 @ X32 )
        = ( k2_struct_0 @ X33 ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('157',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('161',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v2_tops_1 @ X34 @ X35 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X35 ) @ X34 ) @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v2_tops_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_tops_1 @ X1 @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['159','163'])).

thf('165',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['124','125','134'])).

thf('167',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('168',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v3_tops_1 @ X36 @ X37 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X37 @ X36 ) @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('169',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v3_tops_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,(
    v1_tops_1 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['164','165','166','172'])).

thf('174',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['157','158','173'])).

thf('175',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','135','174'])).

thf('176',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('177',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('179',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','179'])).

thf('181',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('184',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('185',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('186',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['157','158','173'])).

thf('188',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('189',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','182','183','186','187','188','189'])).

thf('191',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('193',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    $false ),
    inference(demod,[status(thm)],['46','193'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kntMNmNq47
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.60/2.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.60/2.86  % Solved by: fo/fo7.sh
% 2.60/2.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.60/2.86  % done 6052 iterations in 2.400s
% 2.60/2.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.60/2.86  % SZS output start Refutation
% 2.60/2.86  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 2.60/2.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.60/2.86  thf(sk_A_type, type, sk_A: $i).
% 2.60/2.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.60/2.86  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.60/2.86  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.60/2.86  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.60/2.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.60/2.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.60/2.86  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.60/2.86  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 2.60/2.86  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.60/2.86  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.60/2.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.60/2.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.60/2.86  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 2.60/2.86  thf(d3_struct_0, axiom,
% 2.60/2.86    (![A:$i]:
% 2.60/2.86     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.60/2.86  thf('0', plain,
% 2.60/2.86      (![X23 : $i]:
% 2.60/2.86         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 2.60/2.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.60/2.86  thf('1', plain,
% 2.60/2.86      (![X23 : $i]:
% 2.60/2.86         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 2.60/2.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.60/2.86  thf(t91_tops_1, conjecture,
% 2.60/2.86    (![A:$i]:
% 2.60/2.86     ( ( l1_pre_topc @ A ) =>
% 2.60/2.86       ( ![B:$i]:
% 2.60/2.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.60/2.86           ( ( v3_tops_1 @ B @ A ) =>
% 2.60/2.86             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 2.60/2.86  thf(zf_stmt_0, negated_conjecture,
% 2.60/2.86    (~( ![A:$i]:
% 2.60/2.86        ( ( l1_pre_topc @ A ) =>
% 2.60/2.86          ( ![B:$i]:
% 2.60/2.86            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.60/2.86              ( ( v3_tops_1 @ B @ A ) =>
% 2.60/2.86                ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 2.60/2.86    inference('cnf.neg', [status(esa)], [t91_tops_1])).
% 2.60/2.86  thf('2', plain,
% 2.60/2.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf(d5_subset_1, axiom,
% 2.60/2.86    (![A:$i,B:$i]:
% 2.60/2.86     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.60/2.86       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.60/2.86  thf('3', plain,
% 2.60/2.86      (![X8 : $i, X9 : $i]:
% 2.60/2.86         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 2.60/2.86          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 2.60/2.86      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.60/2.86  thf('4', plain,
% 2.60/2.86      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 2.60/2.86         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 2.60/2.86      inference('sup-', [status(thm)], ['2', '3'])).
% 2.60/2.86  thf('5', plain,
% 2.60/2.86      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1)
% 2.60/2.86          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 2.60/2.86        | ~ (l1_struct_0 @ sk_A))),
% 2.60/2.86      inference('sup+', [status(thm)], ['1', '4'])).
% 2.60/2.86  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf(dt_l1_pre_topc, axiom,
% 2.60/2.86    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.60/2.86  thf('7', plain, (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 2.60/2.86      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.60/2.86  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 2.60/2.86      inference('sup-', [status(thm)], ['6', '7'])).
% 2.60/2.86  thf('9', plain,
% 2.60/2.86      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1)
% 2.60/2.86         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 2.60/2.86      inference('demod', [status(thm)], ['5', '8'])).
% 2.60/2.86  thf(t36_xboole_1, axiom,
% 2.60/2.86    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.60/2.86  thf('10', plain,
% 2.60/2.86      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 2.60/2.86      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.60/2.86  thf(t3_subset, axiom,
% 2.60/2.86    (![A:$i,B:$i]:
% 2.60/2.86     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.60/2.86  thf('11', plain,
% 2.60/2.86      (![X20 : $i, X22 : $i]:
% 2.60/2.86         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 2.60/2.86      inference('cnf', [status(esa)], [t3_subset])).
% 2.60/2.86  thf('12', plain,
% 2.60/2.86      (![X0 : $i, X1 : $i]:
% 2.60/2.86         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.60/2.86      inference('sup-', [status(thm)], ['10', '11'])).
% 2.60/2.86  thf('13', plain,
% 2.60/2.86      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('sup+', [status(thm)], ['9', '12'])).
% 2.60/2.86  thf('14', plain,
% 2.60/2.86      (![X23 : $i]:
% 2.60/2.86         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 2.60/2.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.60/2.86  thf('15', plain,
% 2.60/2.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('16', plain,
% 2.60/2.86      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.60/2.86        | ~ (l1_struct_0 @ sk_A))),
% 2.60/2.86      inference('sup+', [status(thm)], ['14', '15'])).
% 2.60/2.86  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 2.60/2.86      inference('sup-', [status(thm)], ['6', '7'])).
% 2.60/2.86  thf('18', plain,
% 2.60/2.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['16', '17'])).
% 2.60/2.86  thf('19', plain,
% 2.60/2.86      (![X8 : $i, X9 : $i]:
% 2.60/2.86         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 2.60/2.86          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 2.60/2.86      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.60/2.86  thf('20', plain,
% 2.60/2.86      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1)
% 2.60/2.86         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))),
% 2.60/2.86      inference('sup-', [status(thm)], ['18', '19'])).
% 2.60/2.86  thf('21', plain,
% 2.60/2.86      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['13', '20'])).
% 2.60/2.86  thf(dt_k2_pre_topc, axiom,
% 2.60/2.86    (![A:$i,B:$i]:
% 2.60/2.86     ( ( ( l1_pre_topc @ A ) & 
% 2.60/2.86         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.60/2.86       ( m1_subset_1 @
% 2.60/2.86         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.60/2.86  thf('22', plain,
% 2.60/2.86      (![X24 : $i, X25 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X24)
% 2.60/2.86          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 2.60/2.86          | (m1_subset_1 @ (k2_pre_topc @ X24 @ X25) @ 
% 2.60/2.86             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 2.60/2.86      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.60/2.86  thf('23', plain,
% 2.60/2.86      (((m1_subset_1 @ 
% 2.60/2.86         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 2.60/2.86         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.60/2.86        | ~ (l1_pre_topc @ sk_A))),
% 2.60/2.86      inference('sup-', [status(thm)], ['21', '22'])).
% 2.60/2.86  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('25', plain,
% 2.60/2.86      ((m1_subset_1 @ 
% 2.60/2.86        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['23', '24'])).
% 2.60/2.86  thf('26', plain,
% 2.60/2.86      (![X20 : $i, X21 : $i]:
% 2.60/2.86         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 2.60/2.86      inference('cnf', [status(esa)], [t3_subset])).
% 2.60/2.86  thf('27', plain,
% 2.60/2.86      ((r1_tarski @ 
% 2.60/2.86        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 2.60/2.86        (u1_struct_0 @ sk_A))),
% 2.60/2.86      inference('sup-', [status(thm)], ['25', '26'])).
% 2.60/2.86  thf('28', plain,
% 2.60/2.86      (((r1_tarski @ 
% 2.60/2.86         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 2.60/2.86         (k2_struct_0 @ sk_A))
% 2.60/2.86        | ~ (l1_struct_0 @ sk_A))),
% 2.60/2.86      inference('sup+', [status(thm)], ['0', '27'])).
% 2.60/2.86  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 2.60/2.86      inference('sup-', [status(thm)], ['6', '7'])).
% 2.60/2.86  thf('30', plain,
% 2.60/2.86      ((r1_tarski @ 
% 2.60/2.86        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 2.60/2.86        (k2_struct_0 @ sk_A))),
% 2.60/2.86      inference('demod', [status(thm)], ['28', '29'])).
% 2.60/2.86  thf(d10_xboole_0, axiom,
% 2.60/2.86    (![A:$i,B:$i]:
% 2.60/2.86     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.60/2.86  thf('31', plain,
% 2.60/2.86      (![X0 : $i, X2 : $i]:
% 2.60/2.86         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.60/2.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.60/2.86  thf('32', plain,
% 2.60/2.86      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 2.60/2.86           (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 2.60/2.86        | ((k2_struct_0 @ sk_A)
% 2.60/2.86            = (k2_pre_topc @ sk_A @ 
% 2.60/2.86               (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 2.60/2.86      inference('sup-', [status(thm)], ['30', '31'])).
% 2.60/2.86  thf('33', plain,
% 2.60/2.86      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['13', '20'])).
% 2.60/2.86  thf(d3_tops_1, axiom,
% 2.60/2.86    (![A:$i]:
% 2.60/2.86     ( ( l1_pre_topc @ A ) =>
% 2.60/2.86       ( ![B:$i]:
% 2.60/2.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.60/2.86           ( ( v1_tops_1 @ B @ A ) <=>
% 2.60/2.86             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 2.60/2.86  thf('34', plain,
% 2.60/2.86      (![X32 : $i, X33 : $i]:
% 2.60/2.86         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 2.60/2.86          | ((k2_pre_topc @ X33 @ X32) != (k2_struct_0 @ X33))
% 2.60/2.86          | (v1_tops_1 @ X32 @ X33)
% 2.60/2.86          | ~ (l1_pre_topc @ X33))),
% 2.60/2.86      inference('cnf', [status(esa)], [d3_tops_1])).
% 2.60/2.86  thf('35', plain,
% 2.60/2.86      ((~ (l1_pre_topc @ sk_A)
% 2.60/2.86        | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 2.60/2.86        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 2.60/2.86            != (k2_struct_0 @ sk_A)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['33', '34'])).
% 2.60/2.86  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('37', plain,
% 2.60/2.86      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 2.60/2.86        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 2.60/2.86            != (k2_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['35', '36'])).
% 2.60/2.86  thf('38', plain,
% 2.60/2.86      (![X23 : $i]:
% 2.60/2.86         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 2.60/2.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.60/2.86  thf('39', plain,
% 2.60/2.86      (~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('40', plain,
% 2.60/2.86      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 2.60/2.86         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 2.60/2.86      inference('sup-', [status(thm)], ['2', '3'])).
% 2.60/2.86  thf('41', plain,
% 2.60/2.86      (~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 2.60/2.86      inference('demod', [status(thm)], ['39', '40'])).
% 2.60/2.86  thf('42', plain,
% 2.60/2.86      ((~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 2.60/2.86        | ~ (l1_struct_0 @ sk_A))),
% 2.60/2.86      inference('sup-', [status(thm)], ['38', '41'])).
% 2.60/2.86  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 2.60/2.86      inference('sup-', [status(thm)], ['6', '7'])).
% 2.60/2.86  thf('44', plain,
% 2.60/2.86      (~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 2.60/2.86      inference('demod', [status(thm)], ['42', '43'])).
% 2.60/2.86  thf('45', plain,
% 2.60/2.86      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 2.60/2.86         != (k2_struct_0 @ sk_A))),
% 2.60/2.86      inference('clc', [status(thm)], ['37', '44'])).
% 2.60/2.86  thf('46', plain,
% 2.60/2.86      (~ (r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 2.60/2.86          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 2.60/2.86      inference('simplify_reflect-', [status(thm)], ['32', '45'])).
% 2.60/2.86  thf('47', plain,
% 2.60/2.86      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['13', '20'])).
% 2.60/2.86  thf(t44_tops_1, axiom,
% 2.60/2.86    (![A:$i]:
% 2.60/2.86     ( ( l1_pre_topc @ A ) =>
% 2.60/2.86       ( ![B:$i]:
% 2.60/2.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.60/2.86           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 2.60/2.86  thf('48', plain,
% 2.60/2.86      (![X42 : $i, X43 : $i]:
% 2.60/2.86         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 2.60/2.86          | (r1_tarski @ (k1_tops_1 @ X43 @ X42) @ X42)
% 2.60/2.86          | ~ (l1_pre_topc @ X43))),
% 2.60/2.86      inference('cnf', [status(esa)], [t44_tops_1])).
% 2.60/2.86  thf('49', plain,
% 2.60/2.86      ((~ (l1_pre_topc @ sk_A)
% 2.60/2.86        | (r1_tarski @ 
% 2.60/2.86           (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 2.60/2.86           (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['47', '48'])).
% 2.60/2.86  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('51', plain,
% 2.60/2.86      ((r1_tarski @ 
% 2.60/2.86        (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 2.60/2.86        (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))),
% 2.60/2.86      inference('demod', [status(thm)], ['49', '50'])).
% 2.60/2.86  thf('52', plain,
% 2.60/2.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('53', plain,
% 2.60/2.86      (![X24 : $i, X25 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X24)
% 2.60/2.86          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 2.60/2.86          | (m1_subset_1 @ (k2_pre_topc @ X24 @ X25) @ 
% 2.60/2.86             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 2.60/2.86      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.60/2.86  thf('54', plain,
% 2.60/2.86      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.60/2.86         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.60/2.86        | ~ (l1_pre_topc @ sk_A))),
% 2.60/2.86      inference('sup-', [status(thm)], ['52', '53'])).
% 2.60/2.86  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('56', plain,
% 2.60/2.86      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['54', '55'])).
% 2.60/2.86  thf(dt_k3_subset_1, axiom,
% 2.60/2.86    (![A:$i,B:$i]:
% 2.60/2.86     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.60/2.86       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.60/2.86  thf('57', plain,
% 2.60/2.86      (![X10 : $i, X11 : $i]:
% 2.60/2.86         ((m1_subset_1 @ (k3_subset_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))
% 2.60/2.86          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 2.60/2.86      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.60/2.86  thf('58', plain,
% 2.60/2.86      ((m1_subset_1 @ 
% 2.60/2.86        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['56', '57'])).
% 2.60/2.86  thf(t49_pre_topc, axiom,
% 2.60/2.86    (![A:$i]:
% 2.60/2.86     ( ( l1_pre_topc @ A ) =>
% 2.60/2.86       ( ![B:$i]:
% 2.60/2.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.60/2.86           ( ![C:$i]:
% 2.60/2.86             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.60/2.86               ( ( r1_tarski @ B @ C ) =>
% 2.60/2.86                 ( r1_tarski @
% 2.60/2.86                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 2.60/2.86  thf('59', plain,
% 2.60/2.86      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.60/2.86         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 2.60/2.86          | ~ (r1_tarski @ X27 @ X29)
% 2.60/2.86          | (r1_tarski @ (k2_pre_topc @ X28 @ X27) @ (k2_pre_topc @ X28 @ X29))
% 2.60/2.86          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 2.60/2.86          | ~ (l1_pre_topc @ X28))),
% 2.60/2.86      inference('cnf', [status(esa)], [t49_pre_topc])).
% 2.60/2.86  thf('60', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ sk_A)
% 2.60/2.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.60/2.86          | (r1_tarski @ 
% 2.60/2.86             (k2_pre_topc @ sk_A @ 
% 2.60/2.86              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.60/2.86               (k2_pre_topc @ sk_A @ sk_B_1))) @ 
% 2.60/2.86             (k2_pre_topc @ sk_A @ X0))
% 2.60/2.86          | ~ (r1_tarski @ 
% 2.60/2.86               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.60/2.86                (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 2.60/2.86               X0))),
% 2.60/2.86      inference('sup-', [status(thm)], ['58', '59'])).
% 2.60/2.86  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('62', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.60/2.86          | (r1_tarski @ 
% 2.60/2.86             (k2_pre_topc @ sk_A @ 
% 2.60/2.86              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.60/2.86               (k2_pre_topc @ sk_A @ sk_B_1))) @ 
% 2.60/2.86             (k2_pre_topc @ sk_A @ X0))
% 2.60/2.86          | ~ (r1_tarski @ 
% 2.60/2.86               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.60/2.86                (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 2.60/2.86               X0))),
% 2.60/2.86      inference('demod', [status(thm)], ['60', '61'])).
% 2.60/2.86  thf('63', plain,
% 2.60/2.86      (![X23 : $i]:
% 2.60/2.86         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 2.60/2.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.60/2.86  thf(t27_tops_1, axiom,
% 2.60/2.86    (![A:$i]:
% 2.60/2.86     ( ( l1_pre_topc @ A ) =>
% 2.60/2.86       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 2.60/2.86  thf('64', plain,
% 2.60/2.86      (![X41 : $i]:
% 2.60/2.86         (((k2_pre_topc @ X41 @ (k2_struct_0 @ X41)) = (k2_struct_0 @ X41))
% 2.60/2.86          | ~ (l1_pre_topc @ X41))),
% 2.60/2.86      inference('cnf', [status(esa)], [t27_tops_1])).
% 2.60/2.86  thf('65', plain,
% 2.60/2.86      (![X23 : $i]:
% 2.60/2.86         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 2.60/2.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.60/2.86  thf('66', plain,
% 2.60/2.86      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.60/2.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.60/2.86  thf('67', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.60/2.86      inference('simplify', [status(thm)], ['66'])).
% 2.60/2.86  thf('68', plain,
% 2.60/2.86      (![X20 : $i, X22 : $i]:
% 2.60/2.86         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 2.60/2.86      inference('cnf', [status(esa)], [t3_subset])).
% 2.60/2.86  thf('69', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.60/2.86      inference('sup-', [status(thm)], ['67', '68'])).
% 2.60/2.86  thf('70', plain,
% 2.60/2.86      (![X24 : $i, X25 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X24)
% 2.60/2.86          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 2.60/2.86          | (m1_subset_1 @ (k2_pre_topc @ X24 @ X25) @ 
% 2.60/2.86             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 2.60/2.86      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.60/2.86  thf('71', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 2.60/2.86           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.60/2.86          | ~ (l1_pre_topc @ X0))),
% 2.60/2.86      inference('sup-', [status(thm)], ['69', '70'])).
% 2.60/2.86  thf('72', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 2.60/2.86           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.60/2.86          | ~ (l1_struct_0 @ X0)
% 2.60/2.86          | ~ (l1_pre_topc @ X0))),
% 2.60/2.86      inference('sup+', [status(thm)], ['65', '71'])).
% 2.60/2.86  thf('73', plain,
% 2.60/2.86      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 2.60/2.86      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.60/2.86  thf('74', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0)
% 2.60/2.86          | (m1_subset_1 @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 2.60/2.86             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 2.60/2.86      inference('clc', [status(thm)], ['72', '73'])).
% 2.60/2.86  thf('75', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 2.60/2.86           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.60/2.86          | ~ (l1_pre_topc @ X0)
% 2.60/2.86          | ~ (l1_pre_topc @ X0))),
% 2.60/2.86      inference('sup+', [status(thm)], ['64', '74'])).
% 2.60/2.86  thf('76', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0)
% 2.60/2.86          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 2.60/2.86             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 2.60/2.86      inference('simplify', [status(thm)], ['75'])).
% 2.60/2.86  thf('77', plain,
% 2.60/2.86      (![X20 : $i, X21 : $i]:
% 2.60/2.86         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 2.60/2.86      inference('cnf', [status(esa)], [t3_subset])).
% 2.60/2.86  thf('78', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0)
% 2.60/2.86          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['76', '77'])).
% 2.60/2.86  thf('79', plain,
% 2.60/2.86      (![X0 : $i, X2 : $i]:
% 2.60/2.86         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.60/2.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.60/2.86  thf('80', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0)
% 2.60/2.86          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 2.60/2.86          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['78', '79'])).
% 2.60/2.86  thf('81', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (r1_tarski @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 2.60/2.86          | ~ (l1_struct_0 @ X0)
% 2.60/2.86          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0))
% 2.60/2.86          | ~ (l1_pre_topc @ X0))),
% 2.60/2.86      inference('sup-', [status(thm)], ['63', '80'])).
% 2.60/2.86  thf('82', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.60/2.86      inference('simplify', [status(thm)], ['66'])).
% 2.60/2.86  thf('83', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_struct_0 @ X0)
% 2.60/2.86          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0))
% 2.60/2.86          | ~ (l1_pre_topc @ X0))),
% 2.60/2.86      inference('demod', [status(thm)], ['81', '82'])).
% 2.60/2.86  thf('84', plain,
% 2.60/2.86      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 2.60/2.86      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.60/2.86  thf('85', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 2.60/2.86      inference('clc', [status(thm)], ['83', '84'])).
% 2.60/2.86  thf('86', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.60/2.86      inference('sup-', [status(thm)], ['67', '68'])).
% 2.60/2.86  thf('87', plain,
% 2.60/2.86      (![X32 : $i, X33 : $i]:
% 2.60/2.86         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 2.60/2.86          | ~ (v1_tops_1 @ X32 @ X33)
% 2.60/2.86          | ((k2_pre_topc @ X33 @ X32) = (k2_struct_0 @ X33))
% 2.60/2.86          | ~ (l1_pre_topc @ X33))),
% 2.60/2.86      inference('cnf', [status(esa)], [d3_tops_1])).
% 2.60/2.86  thf('88', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0)
% 2.60/2.86          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 2.60/2.86          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 2.60/2.86      inference('sup-', [status(thm)], ['86', '87'])).
% 2.60/2.86  thf('89', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 2.60/2.86      inference('clc', [status(thm)], ['83', '84'])).
% 2.60/2.86  thf('90', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.60/2.86      inference('sup-', [status(thm)], ['67', '68'])).
% 2.60/2.86  thf('91', plain,
% 2.60/2.86      (![X32 : $i, X33 : $i]:
% 2.60/2.86         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 2.60/2.86          | ((k2_pre_topc @ X33 @ X32) != (k2_struct_0 @ X33))
% 2.60/2.86          | (v1_tops_1 @ X32 @ X33)
% 2.60/2.86          | ~ (l1_pre_topc @ X33))),
% 2.60/2.86      inference('cnf', [status(esa)], [d3_tops_1])).
% 2.60/2.86  thf('92', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0)
% 2.60/2.86          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 2.60/2.86          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (k2_struct_0 @ X0)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['90', '91'])).
% 2.60/2.86  thf('93', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) != (k2_struct_0 @ X0))
% 2.60/2.86          | ~ (l1_pre_topc @ X0)
% 2.60/2.86          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 2.60/2.86          | ~ (l1_pre_topc @ X0))),
% 2.60/2.86      inference('sup-', [status(thm)], ['89', '92'])).
% 2.60/2.86  thf('94', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 2.60/2.86          | ~ (l1_pre_topc @ X0)
% 2.60/2.86          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) != (k2_struct_0 @ X0)))),
% 2.60/2.86      inference('simplify', [status(thm)], ['93'])).
% 2.60/2.86  thf('95', plain,
% 2.60/2.86      (![X41 : $i]:
% 2.60/2.86         (((k2_pre_topc @ X41 @ (k2_struct_0 @ X41)) = (k2_struct_0 @ X41))
% 2.60/2.86          | ~ (l1_pre_topc @ X41))),
% 2.60/2.86      inference('cnf', [status(esa)], [t27_tops_1])).
% 2.60/2.86  thf('96', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0) | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 2.60/2.86      inference('clc', [status(thm)], ['94', '95'])).
% 2.60/2.86  thf('97', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 2.60/2.86          | ~ (l1_pre_topc @ X0))),
% 2.60/2.86      inference('clc', [status(thm)], ['88', '96'])).
% 2.60/2.86  thf('98', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 2.60/2.86           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.60/2.86          | ~ (l1_pre_topc @ X0))),
% 2.60/2.86      inference('sup-', [status(thm)], ['69', '70'])).
% 2.60/2.86  thf('99', plain,
% 2.60/2.86      (![X20 : $i, X21 : $i]:
% 2.60/2.86         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 2.60/2.86      inference('cnf', [status(esa)], [t3_subset])).
% 2.60/2.86  thf('100', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0)
% 2.60/2.86          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 2.60/2.86             (u1_struct_0 @ X0)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['98', '99'])).
% 2.60/2.86  thf('101', plain,
% 2.60/2.86      (![X0 : $i, X2 : $i]:
% 2.60/2.86         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.60/2.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.60/2.86  thf('102', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0)
% 2.60/2.86          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 2.60/2.86               (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 2.60/2.86          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 2.60/2.86      inference('sup-', [status(thm)], ['100', '101'])).
% 2.60/2.86  thf('103', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 2.60/2.86          | ~ (l1_pre_topc @ X0)
% 2.60/2.86          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 2.60/2.86          | ~ (l1_pre_topc @ X0))),
% 2.60/2.86      inference('sup-', [status(thm)], ['97', '102'])).
% 2.60/2.86  thf('104', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 2.60/2.86          | ~ (l1_pre_topc @ X0)
% 2.60/2.86          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 2.60/2.86      inference('simplify', [status(thm)], ['103'])).
% 2.60/2.86  thf('105', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (r1_tarski @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 2.60/2.86          | ~ (l1_pre_topc @ X0)
% 2.60/2.86          | ~ (l1_pre_topc @ X0)
% 2.60/2.86          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 2.60/2.86      inference('sup-', [status(thm)], ['85', '104'])).
% 2.60/2.86  thf('106', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.60/2.86      inference('simplify', [status(thm)], ['66'])).
% 2.60/2.86  thf('107', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0)
% 2.60/2.86          | ~ (l1_pre_topc @ X0)
% 2.60/2.86          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 2.60/2.86      inference('demod', [status(thm)], ['105', '106'])).
% 2.60/2.86  thf('108', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 2.60/2.86          | ~ (l1_pre_topc @ X0))),
% 2.60/2.86      inference('simplify', [status(thm)], ['107'])).
% 2.60/2.86  thf('109', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 2.60/2.86      inference('clc', [status(thm)], ['83', '84'])).
% 2.60/2.86  thf('110', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 2.60/2.86           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.60/2.86          | ~ (l1_pre_topc @ X0))),
% 2.60/2.86      inference('sup-', [status(thm)], ['69', '70'])).
% 2.60/2.86  thf('111', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 2.60/2.86           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 2.60/2.86          | ~ (l1_pre_topc @ X0)
% 2.60/2.86          | ~ (l1_pre_topc @ X0))),
% 2.60/2.86      inference('sup+', [status(thm)], ['109', '110'])).
% 2.60/2.86  thf('112', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0)
% 2.60/2.86          | (m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 2.60/2.86             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 2.60/2.86      inference('simplify', [status(thm)], ['111'])).
% 2.60/2.86  thf('113', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 2.60/2.86           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 2.60/2.86          | ~ (l1_pre_topc @ X0)
% 2.60/2.86          | ~ (l1_pre_topc @ X0))),
% 2.60/2.86      inference('sup+', [status(thm)], ['108', '112'])).
% 2.60/2.86  thf('114', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0)
% 2.60/2.86          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 2.60/2.86             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 2.60/2.86      inference('simplify', [status(thm)], ['113'])).
% 2.60/2.86  thf('115', plain,
% 2.60/2.86      (![X20 : $i, X21 : $i]:
% 2.60/2.86         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 2.60/2.86      inference('cnf', [status(esa)], [t3_subset])).
% 2.60/2.86  thf('116', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0)
% 2.60/2.86          | (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['114', '115'])).
% 2.60/2.86  thf('117', plain,
% 2.60/2.86      ((m1_subset_1 @ 
% 2.60/2.86        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['56', '57'])).
% 2.60/2.86  thf('118', plain,
% 2.60/2.86      (![X24 : $i, X25 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X24)
% 2.60/2.86          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 2.60/2.86          | (m1_subset_1 @ (k2_pre_topc @ X24 @ X25) @ 
% 2.60/2.86             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 2.60/2.86      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.60/2.86  thf('119', plain,
% 2.60/2.86      (((m1_subset_1 @ 
% 2.60/2.86         (k2_pre_topc @ sk_A @ 
% 2.60/2.86          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1))) @ 
% 2.60/2.86         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.60/2.86        | ~ (l1_pre_topc @ sk_A))),
% 2.60/2.86      inference('sup-', [status(thm)], ['117', '118'])).
% 2.60/2.86  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('121', plain,
% 2.60/2.86      ((m1_subset_1 @ 
% 2.60/2.86        (k2_pre_topc @ sk_A @ 
% 2.60/2.86         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1))) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['119', '120'])).
% 2.60/2.86  thf('122', plain,
% 2.60/2.86      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['13', '20'])).
% 2.60/2.86  thf(d1_tops_1, axiom,
% 2.60/2.86    (![A:$i]:
% 2.60/2.86     ( ( l1_pre_topc @ A ) =>
% 2.60/2.86       ( ![B:$i]:
% 2.60/2.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.60/2.86           ( ( k1_tops_1 @ A @ B ) =
% 2.60/2.86             ( k3_subset_1 @
% 2.60/2.86               ( u1_struct_0 @ A ) @ 
% 2.60/2.86               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 2.60/2.86  thf('123', plain,
% 2.60/2.86      (![X30 : $i, X31 : $i]:
% 2.60/2.86         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 2.60/2.86          | ((k1_tops_1 @ X31 @ X30)
% 2.60/2.86              = (k3_subset_1 @ (u1_struct_0 @ X31) @ 
% 2.60/2.86                 (k2_pre_topc @ X31 @ (k3_subset_1 @ (u1_struct_0 @ X31) @ X30))))
% 2.60/2.86          | ~ (l1_pre_topc @ X31))),
% 2.60/2.86      inference('cnf', [status(esa)], [d1_tops_1])).
% 2.60/2.86  thf('124', plain,
% 2.60/2.86      ((~ (l1_pre_topc @ sk_A)
% 2.60/2.86        | ((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 2.60/2.86            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.60/2.86               (k2_pre_topc @ sk_A @ 
% 2.60/2.86                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.60/2.86                 (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))))))),
% 2.60/2.86      inference('sup-', [status(thm)], ['122', '123'])).
% 2.60/2.86  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('126', plain,
% 2.60/2.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf(involutiveness_k3_subset_1, axiom,
% 2.60/2.86    (![A:$i,B:$i]:
% 2.60/2.86     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.60/2.86       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 2.60/2.86  thf('127', plain,
% 2.60/2.86      (![X12 : $i, X13 : $i]:
% 2.60/2.86         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 2.60/2.86          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 2.60/2.86      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.60/2.86  thf('128', plain,
% 2.60/2.86      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.60/2.86         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 2.60/2.86      inference('sup-', [status(thm)], ['126', '127'])).
% 2.60/2.86  thf('129', plain,
% 2.60/2.86      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 2.60/2.86         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 2.60/2.86      inference('sup-', [status(thm)], ['2', '3'])).
% 2.60/2.86  thf('130', plain,
% 2.60/2.86      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1)
% 2.60/2.86         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 2.60/2.86      inference('demod', [status(thm)], ['5', '8'])).
% 2.60/2.86  thf('131', plain,
% 2.60/2.86      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 2.60/2.86         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1))),
% 2.60/2.86      inference('demod', [status(thm)], ['129', '130'])).
% 2.60/2.86  thf('132', plain,
% 2.60/2.86      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B_1)
% 2.60/2.86         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))),
% 2.60/2.86      inference('sup-', [status(thm)], ['18', '19'])).
% 2.60/2.86  thf('133', plain,
% 2.60/2.86      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 2.60/2.86         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))),
% 2.60/2.86      inference('demod', [status(thm)], ['131', '132'])).
% 2.60/2.86  thf('134', plain,
% 2.60/2.86      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.60/2.86         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 2.60/2.86      inference('demod', [status(thm)], ['128', '133'])).
% 2.60/2.86  thf('135', plain,
% 2.60/2.86      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 2.60/2.86         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 2.60/2.86      inference('demod', [status(thm)], ['124', '125', '134'])).
% 2.60/2.86  thf('136', plain,
% 2.60/2.86      (![X23 : $i]:
% 2.60/2.86         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 2.60/2.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.60/2.86  thf('137', plain,
% 2.60/2.86      ((m1_subset_1 @ 
% 2.60/2.86        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['56', '57'])).
% 2.60/2.86  thf('138', plain,
% 2.60/2.86      (((m1_subset_1 @ 
% 2.60/2.86         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 2.60/2.86         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.60/2.86        | ~ (l1_struct_0 @ sk_A))),
% 2.60/2.86      inference('sup+', [status(thm)], ['136', '137'])).
% 2.60/2.86  thf('139', plain, ((l1_struct_0 @ sk_A)),
% 2.60/2.86      inference('sup-', [status(thm)], ['6', '7'])).
% 2.60/2.86  thf('140', plain,
% 2.60/2.86      ((m1_subset_1 @ 
% 2.60/2.86        (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['138', '139'])).
% 2.60/2.86  thf('141', plain,
% 2.60/2.86      (![X23 : $i]:
% 2.60/2.86         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 2.60/2.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.60/2.86  thf('142', plain,
% 2.60/2.86      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['54', '55'])).
% 2.60/2.86  thf('143', plain,
% 2.60/2.86      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.60/2.86         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.60/2.86        | ~ (l1_struct_0 @ sk_A))),
% 2.60/2.86      inference('sup+', [status(thm)], ['141', '142'])).
% 2.60/2.86  thf('144', plain, ((l1_struct_0 @ sk_A)),
% 2.60/2.86      inference('sup-', [status(thm)], ['6', '7'])).
% 2.60/2.86  thf('145', plain,
% 2.60/2.86      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['143', '144'])).
% 2.60/2.86  thf('146', plain,
% 2.60/2.86      (![X8 : $i, X9 : $i]:
% 2.60/2.86         (((k3_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))
% 2.60/2.86          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 2.60/2.86      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.60/2.86  thf('147', plain,
% 2.60/2.86      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1))
% 2.60/2.86         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['145', '146'])).
% 2.60/2.86  thf('148', plain,
% 2.60/2.86      ((m1_subset_1 @ 
% 2.60/2.86        (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['140', '147'])).
% 2.60/2.86  thf('149', plain,
% 2.60/2.86      (![X23 : $i]:
% 2.60/2.86         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 2.60/2.86      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.60/2.86  thf('150', plain,
% 2.60/2.86      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 2.60/2.86         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 2.60/2.86      inference('demod', [status(thm)], ['124', '125', '134'])).
% 2.60/2.86  thf('151', plain,
% 2.60/2.86      ((((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 2.60/2.86          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)))
% 2.60/2.86        | ~ (l1_struct_0 @ sk_A))),
% 2.60/2.86      inference('sup+', [status(thm)], ['149', '150'])).
% 2.60/2.86  thf('152', plain,
% 2.60/2.86      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1))
% 2.60/2.86         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['145', '146'])).
% 2.60/2.86  thf('153', plain, ((l1_struct_0 @ sk_A)),
% 2.60/2.86      inference('sup-', [status(thm)], ['6', '7'])).
% 2.60/2.86  thf('154', plain,
% 2.60/2.86      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 2.60/2.86         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 2.60/2.86      inference('demod', [status(thm)], ['151', '152', '153'])).
% 2.60/2.86  thf('155', plain,
% 2.60/2.86      ((m1_subset_1 @ 
% 2.60/2.86        (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['148', '154'])).
% 2.60/2.86  thf('156', plain,
% 2.60/2.86      (![X32 : $i, X33 : $i]:
% 2.60/2.86         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 2.60/2.86          | ~ (v1_tops_1 @ X32 @ X33)
% 2.60/2.86          | ((k2_pre_topc @ X33 @ X32) = (k2_struct_0 @ X33))
% 2.60/2.86          | ~ (l1_pre_topc @ X33))),
% 2.60/2.86      inference('cnf', [status(esa)], [d3_tops_1])).
% 2.60/2.86  thf('157', plain,
% 2.60/2.86      ((~ (l1_pre_topc @ sk_A)
% 2.60/2.86        | ((k2_pre_topc @ sk_A @ 
% 2.60/2.86            (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 2.60/2.86            = (k2_struct_0 @ sk_A))
% 2.60/2.86        | ~ (v1_tops_1 @ 
% 2.60/2.86             (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 2.60/2.86             sk_A))),
% 2.60/2.86      inference('sup-', [status(thm)], ['155', '156'])).
% 2.60/2.86  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('159', plain,
% 2.60/2.86      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['143', '144'])).
% 2.60/2.86  thf('160', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 2.60/2.86      inference('clc', [status(thm)], ['83', '84'])).
% 2.60/2.86  thf(d4_tops_1, axiom,
% 2.60/2.86    (![A:$i]:
% 2.60/2.86     ( ( l1_pre_topc @ A ) =>
% 2.60/2.86       ( ![B:$i]:
% 2.60/2.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.60/2.86           ( ( v2_tops_1 @ B @ A ) <=>
% 2.60/2.86             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 2.60/2.86  thf('161', plain,
% 2.60/2.86      (![X34 : $i, X35 : $i]:
% 2.60/2.86         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 2.60/2.86          | ~ (v2_tops_1 @ X34 @ X35)
% 2.60/2.86          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X35) @ X34) @ X35)
% 2.60/2.86          | ~ (l1_pre_topc @ X35))),
% 2.60/2.86      inference('cnf', [status(esa)], [d4_tops_1])).
% 2.60/2.86  thf('162', plain,
% 2.60/2.86      (![X0 : $i, X1 : $i]:
% 2.60/2.86         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 2.60/2.86          | ~ (l1_pre_topc @ X0)
% 2.60/2.86          | ~ (l1_pre_topc @ X0)
% 2.60/2.86          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 2.60/2.86          | ~ (v2_tops_1 @ X1 @ X0))),
% 2.60/2.86      inference('sup-', [status(thm)], ['160', '161'])).
% 2.60/2.86  thf('163', plain,
% 2.60/2.86      (![X0 : $i, X1 : $i]:
% 2.60/2.86         (~ (v2_tops_1 @ X1 @ X0)
% 2.60/2.86          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 2.60/2.86          | ~ (l1_pre_topc @ X0)
% 2.60/2.86          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 2.60/2.86      inference('simplify', [status(thm)], ['162'])).
% 2.60/2.86  thf('164', plain,
% 2.60/2.86      ((~ (l1_pre_topc @ sk_A)
% 2.60/2.86        | (v1_tops_1 @ 
% 2.60/2.86           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 2.60/2.86           sk_A)
% 2.60/2.86        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_A))),
% 2.60/2.86      inference('sup-', [status(thm)], ['159', '163'])).
% 2.60/2.86  thf('165', plain, ((l1_pre_topc @ sk_A)),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('166', plain,
% 2.60/2.86      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 2.60/2.86         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 2.60/2.86      inference('demod', [status(thm)], ['124', '125', '134'])).
% 2.60/2.86  thf('167', plain,
% 2.60/2.86      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf(d5_tops_1, axiom,
% 2.60/2.86    (![A:$i]:
% 2.60/2.86     ( ( l1_pre_topc @ A ) =>
% 2.60/2.86       ( ![B:$i]:
% 2.60/2.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.60/2.86           ( ( v3_tops_1 @ B @ A ) <=>
% 2.60/2.86             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 2.60/2.86  thf('168', plain,
% 2.60/2.86      (![X36 : $i, X37 : $i]:
% 2.60/2.86         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 2.60/2.86          | ~ (v3_tops_1 @ X36 @ X37)
% 2.60/2.86          | (v2_tops_1 @ (k2_pre_topc @ X37 @ X36) @ X37)
% 2.60/2.86          | ~ (l1_pre_topc @ X37))),
% 2.60/2.86      inference('cnf', [status(esa)], [d5_tops_1])).
% 2.60/2.86  thf('169', plain,
% 2.60/2.86      ((~ (l1_pre_topc @ sk_A)
% 2.60/2.86        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_A)
% 2.60/2.86        | ~ (v3_tops_1 @ sk_B_1 @ sk_A))),
% 2.60/2.86      inference('sup-', [status(thm)], ['167', '168'])).
% 2.60/2.86  thf('170', plain, ((l1_pre_topc @ sk_A)),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('171', plain, ((v3_tops_1 @ sk_B_1 @ sk_A)),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('172', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_A)),
% 2.60/2.86      inference('demod', [status(thm)], ['169', '170', '171'])).
% 2.60/2.86  thf('173', plain,
% 2.60/2.86      ((v1_tops_1 @ 
% 2.60/2.86        (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 2.60/2.86        sk_A)),
% 2.60/2.86      inference('demod', [status(thm)], ['164', '165', '166', '172'])).
% 2.60/2.86  thf('174', plain,
% 2.60/2.86      (((k2_pre_topc @ sk_A @ 
% 2.60/2.86         (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 2.60/2.86         = (k2_struct_0 @ sk_A))),
% 2.60/2.86      inference('demod', [status(thm)], ['157', '158', '173'])).
% 2.60/2.86  thf('175', plain,
% 2.60/2.86      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 2.60/2.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.86      inference('demod', [status(thm)], ['121', '135', '174'])).
% 2.60/2.86  thf('176', plain,
% 2.60/2.86      (![X20 : $i, X21 : $i]:
% 2.60/2.86         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 2.60/2.86      inference('cnf', [status(esa)], [t3_subset])).
% 2.60/2.86  thf('177', plain,
% 2.60/2.86      ((r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 2.60/2.86      inference('sup-', [status(thm)], ['175', '176'])).
% 2.60/2.86  thf('178', plain,
% 2.60/2.86      (![X0 : $i, X2 : $i]:
% 2.60/2.86         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.60/2.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.60/2.86  thf('179', plain,
% 2.60/2.86      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 2.60/2.86        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['177', '178'])).
% 2.60/2.86  thf('180', plain,
% 2.60/2.86      ((~ (l1_pre_topc @ sk_A) | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['116', '179'])).
% 2.60/2.86  thf('181', plain, ((l1_pre_topc @ sk_A)),
% 2.60/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.86  thf('182', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.60/2.86      inference('demod', [status(thm)], ['180', '181'])).
% 2.60/2.86  thf('183', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.60/2.86      inference('demod', [status(thm)], ['180', '181'])).
% 2.60/2.86  thf('184', plain,
% 2.60/2.86      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1))
% 2.60/2.86         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 2.60/2.86      inference('sup-', [status(thm)], ['145', '146'])).
% 2.60/2.86  thf('185', plain,
% 2.60/2.86      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1))
% 2.60/2.86         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 2.60/2.86      inference('demod', [status(thm)], ['151', '152', '153'])).
% 2.60/2.86  thf('186', plain,
% 2.60/2.86      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1))
% 2.60/2.86         = (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 2.60/2.86      inference('demod', [status(thm)], ['184', '185'])).
% 2.60/2.86  thf('187', plain,
% 2.60/2.86      (((k2_pre_topc @ sk_A @ 
% 2.60/2.86         (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 2.60/2.86         = (k2_struct_0 @ sk_A))),
% 2.60/2.86      inference('demod', [status(thm)], ['157', '158', '173'])).
% 2.60/2.86  thf('188', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.60/2.86      inference('demod', [status(thm)], ['180', '181'])).
% 2.60/2.86  thf('189', plain,
% 2.60/2.86      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B_1))
% 2.60/2.86         = (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 2.60/2.86      inference('demod', [status(thm)], ['184', '185'])).
% 2.60/2.86  thf('190', plain,
% 2.60/2.86      (![X0 : $i]:
% 2.60/2.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.60/2.86          | (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ X0))
% 2.60/2.86          | ~ (r1_tarski @ 
% 2.60/2.86               (k1_tops_1 @ sk_A @ 
% 2.60/2.86                (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)) @ 
% 2.60/2.86               X0))),
% 2.60/2.86      inference('demod', [status(thm)],
% 2.60/2.86                ['62', '182', '183', '186', '187', '188', '189'])).
% 2.60/2.86  thf('191', plain,
% 2.60/2.86      (((r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 2.60/2.86         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 2.60/2.86        | ~ (m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ 
% 2.60/2.86             (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 2.60/2.86      inference('sup-', [status(thm)], ['51', '190'])).
% 2.60/2.86  thf('192', plain,
% 2.60/2.86      (![X0 : $i, X1 : $i]:
% 2.60/2.86         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.60/2.86      inference('sup-', [status(thm)], ['10', '11'])).
% 2.60/2.86  thf('193', plain,
% 2.60/2.86      ((r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 2.60/2.86        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 2.60/2.86      inference('demod', [status(thm)], ['191', '192'])).
% 2.60/2.86  thf('194', plain, ($false), inference('demod', [status(thm)], ['46', '193'])).
% 2.60/2.86  
% 2.60/2.86  % SZS output end Refutation
% 2.60/2.86  
% 2.60/2.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
