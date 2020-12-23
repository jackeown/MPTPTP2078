%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TAKoKnnrXw

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:29 EST 2020

% Result     : Theorem 17.00s
% Output     : Refutation 17.00s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 491 expanded)
%              Number of leaves         :   40 ( 168 expanded)
%              Depth                    :   20
%              Number of atoms          : 1623 (4552 expanded)
%              Number of equality atoms :   63 ( 148 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ~ ( r1_tarski @ X57 @ ( k2_tops_1 @ X58 @ X57 ) )
      | ( v2_tops_1 @ X57 @ X58 )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('6',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v2_tops_1 @ X47 @ X48 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X48 ) @ X47 ) @ X48 )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('15',plain,(
    ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['12','15'])).

thf('17',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['4','16'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X40: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('21',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X52 @ X51 ) @ X51 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( l1_pre_topc @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X43 @ X44 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('29',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23
        = ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('34',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23
        = ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['34','40'])).

thf('42',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43','44','47'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('50',plain,(
    ! [X40: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t36_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf('52',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X38 @ X37 ) @ X39 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X38 @ X39 ) @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 )
      | ( r1_tarski @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('55',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B ) @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','57'])).

thf('59',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43','44','47'])).

thf('60',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43','44','47'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','64'])).

thf('66',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('67',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('73',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('75',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X40: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['71','78'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('80',plain,(
    ! [X30: $i,X31: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k1_tops_1 @ X46 @ X45 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X46 ) @ ( k2_pre_topc @ X46 @ ( k3_subset_1 @ ( u1_struct_0 @ X46 ) @ X45 ) ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['71','78'])).

thf('87',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('91',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['71','78'])).

thf('98',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('99',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X33 @ ( k3_subset_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('102',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['95','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['85','88','89','94','106'])).

thf('108',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_B ) ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['70','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('110',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('111',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','111'])).

thf('113',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('117',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('119',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X56 @ ( k2_pre_topc @ X56 @ X55 ) ) @ ( k2_tops_1 @ X56 @ X55 ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('120',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('124',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ~ ( v2_tops_1 @ X57 @ X58 )
      | ( r1_tarski @ X57 @ ( k2_tops_1 @ X58 @ X57 ) )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('125',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('128',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( v3_tops_1 @ X49 @ X50 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X50 @ X49 ) @ X50 )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('129',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126','132'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('134',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['122','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('138',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['137','140'])).

thf('142',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','145'])).

thf('147',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['117','146'])).

thf('148',plain,(
    $false ),
    inference(demod,[status(thm)],['17','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TAKoKnnrXw
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 17.00/17.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.00/17.21  % Solved by: fo/fo7.sh
% 17.00/17.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.00/17.21  % done 26623 iterations in 16.753s
% 17.00/17.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.00/17.21  % SZS output start Refutation
% 17.00/17.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.00/17.21  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 17.00/17.21  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 17.00/17.21  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 17.00/17.21  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 17.00/17.21  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 17.00/17.21  thf(sk_A_type, type, sk_A: $i).
% 17.00/17.21  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 17.00/17.21  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 17.00/17.21  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 17.00/17.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 17.00/17.21  thf(sk_B_type, type, sk_B: $i).
% 17.00/17.21  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 17.00/17.21  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 17.00/17.21  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 17.00/17.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.00/17.21  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 17.00/17.21  thf(t91_tops_1, conjecture,
% 17.00/17.21    (![A:$i]:
% 17.00/17.21     ( ( l1_pre_topc @ A ) =>
% 17.00/17.21       ( ![B:$i]:
% 17.00/17.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.00/17.21           ( ( v3_tops_1 @ B @ A ) =>
% 17.00/17.21             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 17.00/17.21  thf(zf_stmt_0, negated_conjecture,
% 17.00/17.21    (~( ![A:$i]:
% 17.00/17.21        ( ( l1_pre_topc @ A ) =>
% 17.00/17.21          ( ![B:$i]:
% 17.00/17.21            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.00/17.21              ( ( v3_tops_1 @ B @ A ) =>
% 17.00/17.21                ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 17.00/17.21    inference('cnf.neg', [status(esa)], [t91_tops_1])).
% 17.00/17.21  thf('0', plain,
% 17.00/17.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf(t88_tops_1, axiom,
% 17.00/17.21    (![A:$i]:
% 17.00/17.21     ( ( l1_pre_topc @ A ) =>
% 17.00/17.21       ( ![B:$i]:
% 17.00/17.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.00/17.21           ( ( v2_tops_1 @ B @ A ) <=>
% 17.00/17.21             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 17.00/17.21  thf('1', plain,
% 17.00/17.21      (![X57 : $i, X58 : $i]:
% 17.00/17.21         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 17.00/17.21          | ~ (r1_tarski @ X57 @ (k2_tops_1 @ X58 @ X57))
% 17.00/17.21          | (v2_tops_1 @ X57 @ X58)
% 17.00/17.21          | ~ (l1_pre_topc @ X58))),
% 17.00/17.21      inference('cnf', [status(esa)], [t88_tops_1])).
% 17.00/17.21  thf('2', plain,
% 17.00/17.21      ((~ (l1_pre_topc @ sk_A)
% 17.00/17.21        | (v2_tops_1 @ sk_B @ sk_A)
% 17.00/17.21        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['0', '1'])).
% 17.00/17.21  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf('4', plain,
% 17.00/17.21      (((v2_tops_1 @ sk_B @ sk_A)
% 17.00/17.21        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 17.00/17.21      inference('demod', [status(thm)], ['2', '3'])).
% 17.00/17.21  thf('5', plain,
% 17.00/17.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf(d4_tops_1, axiom,
% 17.00/17.21    (![A:$i]:
% 17.00/17.21     ( ( l1_pre_topc @ A ) =>
% 17.00/17.21       ( ![B:$i]:
% 17.00/17.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.00/17.21           ( ( v2_tops_1 @ B @ A ) <=>
% 17.00/17.21             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 17.00/17.21  thf('6', plain,
% 17.00/17.21      (![X47 : $i, X48 : $i]:
% 17.00/17.21         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 17.00/17.21          | ~ (v2_tops_1 @ X47 @ X48)
% 17.00/17.21          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X48) @ X47) @ X48)
% 17.00/17.21          | ~ (l1_pre_topc @ X48))),
% 17.00/17.21      inference('cnf', [status(esa)], [d4_tops_1])).
% 17.00/17.21  thf('7', plain,
% 17.00/17.21      ((~ (l1_pre_topc @ sk_A)
% 17.00/17.21        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 17.00/17.21        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 17.00/17.21      inference('sup-', [status(thm)], ['5', '6'])).
% 17.00/17.21  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf('9', plain,
% 17.00/17.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf(d5_subset_1, axiom,
% 17.00/17.21    (![A:$i,B:$i]:
% 17.00/17.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 17.00/17.21       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 17.00/17.21  thf('10', plain,
% 17.00/17.21      (![X28 : $i, X29 : $i]:
% 17.00/17.21         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 17.00/17.21          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 17.00/17.21      inference('cnf', [status(esa)], [d5_subset_1])).
% 17.00/17.21  thf('11', plain,
% 17.00/17.21      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 17.00/17.21         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 17.00/17.21      inference('sup-', [status(thm)], ['9', '10'])).
% 17.00/17.21  thf('12', plain,
% 17.00/17.21      (((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 17.00/17.21        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 17.00/17.21      inference('demod', [status(thm)], ['7', '8', '11'])).
% 17.00/17.21  thf('13', plain,
% 17.00/17.21      (~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf('14', plain,
% 17.00/17.21      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 17.00/17.21         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 17.00/17.21      inference('sup-', [status(thm)], ['9', '10'])).
% 17.00/17.21  thf('15', plain,
% 17.00/17.21      (~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 17.00/17.21      inference('demod', [status(thm)], ['13', '14'])).
% 17.00/17.21  thf('16', plain, (~ (v2_tops_1 @ sk_B @ sk_A)),
% 17.00/17.21      inference('clc', [status(thm)], ['12', '15'])).
% 17.00/17.21  thf('17', plain, (~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 17.00/17.21      inference('clc', [status(thm)], ['4', '16'])).
% 17.00/17.21  thf(t36_xboole_1, axiom,
% 17.00/17.21    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 17.00/17.21  thf('18', plain,
% 17.00/17.21      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 17.00/17.21      inference('cnf', [status(esa)], [t36_xboole_1])).
% 17.00/17.21  thf(t3_subset, axiom,
% 17.00/17.21    (![A:$i,B:$i]:
% 17.00/17.21     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 17.00/17.21  thf('19', plain,
% 17.00/17.21      (![X40 : $i, X42 : $i]:
% 17.00/17.21         ((m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X42)) | ~ (r1_tarski @ X40 @ X42))),
% 17.00/17.21      inference('cnf', [status(esa)], [t3_subset])).
% 17.00/17.21  thf('20', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]:
% 17.00/17.21         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 17.00/17.21      inference('sup-', [status(thm)], ['18', '19'])).
% 17.00/17.21  thf(t44_tops_1, axiom,
% 17.00/17.21    (![A:$i]:
% 17.00/17.21     ( ( l1_pre_topc @ A ) =>
% 17.00/17.21       ( ![B:$i]:
% 17.00/17.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.00/17.21           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 17.00/17.21  thf('21', plain,
% 17.00/17.21      (![X51 : $i, X52 : $i]:
% 17.00/17.21         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 17.00/17.21          | (r1_tarski @ (k1_tops_1 @ X52 @ X51) @ X51)
% 17.00/17.21          | ~ (l1_pre_topc @ X52))),
% 17.00/17.21      inference('cnf', [status(esa)], [t44_tops_1])).
% 17.00/17.21  thf('22', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]:
% 17.00/17.21         (~ (l1_pre_topc @ X0)
% 17.00/17.21          | (r1_tarski @ 
% 17.00/17.21             (k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 17.00/17.21             (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['20', '21'])).
% 17.00/17.21  thf('23', plain,
% 17.00/17.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf(dt_k2_pre_topc, axiom,
% 17.00/17.21    (![A:$i,B:$i]:
% 17.00/17.21     ( ( ( l1_pre_topc @ A ) & 
% 17.00/17.21         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 17.00/17.21       ( m1_subset_1 @
% 17.00/17.21         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 17.00/17.21  thf('24', plain,
% 17.00/17.21      (![X43 : $i, X44 : $i]:
% 17.00/17.21         (~ (l1_pre_topc @ X43)
% 17.00/17.21          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 17.00/17.21          | (m1_subset_1 @ (k2_pre_topc @ X43 @ X44) @ 
% 17.00/17.21             (k1_zfmisc_1 @ (u1_struct_0 @ X43))))),
% 17.00/17.21      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 17.00/17.21  thf('25', plain,
% 17.00/17.21      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 17.00/17.21         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.00/17.21        | ~ (l1_pre_topc @ sk_A))),
% 17.00/17.21      inference('sup-', [status(thm)], ['23', '24'])).
% 17.00/17.21  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf('27', plain,
% 17.00/17.21      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 17.00/17.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('demod', [status(thm)], ['25', '26'])).
% 17.00/17.21  thf('28', plain,
% 17.00/17.21      (![X28 : $i, X29 : $i]:
% 17.00/17.21         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 17.00/17.21          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 17.00/17.21      inference('cnf', [status(esa)], [d5_subset_1])).
% 17.00/17.21  thf('29', plain,
% 17.00/17.21      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 17.00/17.21         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['27', '28'])).
% 17.00/17.21  thf('30', plain,
% 17.00/17.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf('31', plain,
% 17.00/17.21      (![X40 : $i, X41 : $i]:
% 17.00/17.21         ((r1_tarski @ X40 @ X41) | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 17.00/17.21      inference('cnf', [status(esa)], [t3_subset])).
% 17.00/17.21  thf('32', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 17.00/17.21      inference('sup-', [status(thm)], ['30', '31'])).
% 17.00/17.21  thf(t45_xboole_1, axiom,
% 17.00/17.21    (![A:$i,B:$i]:
% 17.00/17.21     ( ( r1_tarski @ A @ B ) =>
% 17.00/17.21       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 17.00/17.21  thf('33', plain,
% 17.00/17.21      (![X22 : $i, X23 : $i]:
% 17.00/17.21         (((X23) = (k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))
% 17.00/17.21          | ~ (r1_tarski @ X22 @ X23))),
% 17.00/17.21      inference('cnf', [status(esa)], [t45_xboole_1])).
% 17.00/17.21  thf('34', plain,
% 17.00/17.21      (((u1_struct_0 @ sk_A)
% 17.00/17.21         = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['32', '33'])).
% 17.00/17.21  thf(d10_xboole_0, axiom,
% 17.00/17.21    (![A:$i,B:$i]:
% 17.00/17.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 17.00/17.21  thf('35', plain,
% 17.00/17.21      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 17.00/17.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 17.00/17.21  thf('36', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 17.00/17.21      inference('simplify', [status(thm)], ['35'])).
% 17.00/17.21  thf(t10_xboole_1, axiom,
% 17.00/17.21    (![A:$i,B:$i,C:$i]:
% 17.00/17.21     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 17.00/17.21  thf('37', plain,
% 17.00/17.21      (![X5 : $i, X6 : $i, X7 : $i]:
% 17.00/17.21         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 17.00/17.21      inference('cnf', [status(esa)], [t10_xboole_1])).
% 17.00/17.21  thf('38', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 17.00/17.21      inference('sup-', [status(thm)], ['36', '37'])).
% 17.00/17.21  thf('39', plain,
% 17.00/17.21      (![X22 : $i, X23 : $i]:
% 17.00/17.21         (((X23) = (k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))
% 17.00/17.21          | ~ (r1_tarski @ X22 @ X23))),
% 17.00/17.21      inference('cnf', [status(esa)], [t45_xboole_1])).
% 17.00/17.21  thf('40', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]:
% 17.00/17.21         ((k2_xboole_0 @ X1 @ X0)
% 17.00/17.21           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['38', '39'])).
% 17.00/17.21  thf('41', plain,
% 17.00/17.21      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 17.00/17.21         = (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 17.00/17.21            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 17.00/17.21             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 17.00/17.21      inference('sup+', [status(thm)], ['34', '40'])).
% 17.00/17.21  thf('42', plain,
% 17.00/17.21      (((u1_struct_0 @ sk_A)
% 17.00/17.21         = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['32', '33'])).
% 17.00/17.21  thf(t48_xboole_1, axiom,
% 17.00/17.21    (![A:$i,B:$i]:
% 17.00/17.21     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 17.00/17.21  thf('43', plain,
% 17.00/17.21      (![X24 : $i, X25 : $i]:
% 17.00/17.21         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 17.00/17.21           = (k3_xboole_0 @ X24 @ X25))),
% 17.00/17.21      inference('cnf', [status(esa)], [t48_xboole_1])).
% 17.00/17.21  thf(commutativity_k3_xboole_0, axiom,
% 17.00/17.21    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 17.00/17.21  thf('44', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.00/17.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 17.00/17.21  thf('45', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 17.00/17.21      inference('sup-', [status(thm)], ['30', '31'])).
% 17.00/17.21  thf(t28_xboole_1, axiom,
% 17.00/17.21    (![A:$i,B:$i]:
% 17.00/17.21     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 17.00/17.21  thf('46', plain,
% 17.00/17.21      (![X11 : $i, X12 : $i]:
% 17.00/17.21         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 17.00/17.21      inference('cnf', [status(esa)], [t28_xboole_1])).
% 17.00/17.21  thf('47', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 17.00/17.21      inference('sup-', [status(thm)], ['45', '46'])).
% 17.00/17.21  thf('48', plain,
% 17.00/17.21      (((u1_struct_0 @ sk_A)
% 17.00/17.21         = (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B))),
% 17.00/17.21      inference('demod', [status(thm)], ['41', '42', '43', '44', '47'])).
% 17.00/17.21  thf(t7_xboole_1, axiom,
% 17.00/17.21    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 17.00/17.21  thf('49', plain,
% 17.00/17.21      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 17.00/17.21      inference('cnf', [status(esa)], [t7_xboole_1])).
% 17.00/17.21  thf('50', plain,
% 17.00/17.21      (![X40 : $i, X42 : $i]:
% 17.00/17.21         ((m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X42)) | ~ (r1_tarski @ X40 @ X42))),
% 17.00/17.21      inference('cnf', [status(esa)], [t3_subset])).
% 17.00/17.21  thf('51', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]:
% 17.00/17.21         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['49', '50'])).
% 17.00/17.21  thf(t36_subset_1, axiom,
% 17.00/17.21    (![A:$i,B:$i]:
% 17.00/17.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 17.00/17.21       ( ![C:$i]:
% 17.00/17.21         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 17.00/17.21           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 17.00/17.21             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 17.00/17.21  thf('52', plain,
% 17.00/17.21      (![X37 : $i, X38 : $i, X39 : $i]:
% 17.00/17.21         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 17.00/17.21          | (r1_tarski @ (k3_subset_1 @ X38 @ X37) @ X39)
% 17.00/17.21          | ~ (r1_tarski @ (k3_subset_1 @ X38 @ X39) @ X37)
% 17.00/17.21          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 17.00/17.21      inference('cnf', [status(esa)], [t36_subset_1])).
% 17.00/17.21  thf('53', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.00/17.21         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 17.00/17.21          | ~ (r1_tarski @ (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1)
% 17.00/17.21          | (r1_tarski @ (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X2))),
% 17.00/17.21      inference('sup-', [status(thm)], ['51', '52'])).
% 17.00/17.21  thf('54', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]:
% 17.00/17.21         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['49', '50'])).
% 17.00/17.21  thf('55', plain,
% 17.00/17.21      (![X28 : $i, X29 : $i]:
% 17.00/17.21         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 17.00/17.21          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 17.00/17.21      inference('cnf', [status(esa)], [d5_subset_1])).
% 17.00/17.21  thf('56', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]:
% 17.00/17.21         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 17.00/17.21           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 17.00/17.21      inference('sup-', [status(thm)], ['54', '55'])).
% 17.00/17.21  thf('57', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.00/17.21         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 17.00/17.21          | ~ (r1_tarski @ (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1)
% 17.00/17.21          | (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X2))),
% 17.00/17.21      inference('demod', [status(thm)], ['53', '56'])).
% 17.00/17.21  thf('58', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.00/17.21          | (r1_tarski @ 
% 17.00/17.21             (k4_xboole_0 @ 
% 17.00/17.21              (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B) @ 
% 17.00/17.21              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 17.00/17.21             X0)
% 17.00/17.21          | ~ (r1_tarski @ 
% 17.00/17.21               (k3_subset_1 @ 
% 17.00/17.21                (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 17.00/17.21                 sk_B) @ 
% 17.00/17.21                X0) @ 
% 17.00/17.21               (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['48', '57'])).
% 17.00/17.21  thf('59', plain,
% 17.00/17.21      (((u1_struct_0 @ sk_A)
% 17.00/17.21         = (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B))),
% 17.00/17.21      inference('demod', [status(thm)], ['41', '42', '43', '44', '47'])).
% 17.00/17.21  thf('60', plain,
% 17.00/17.21      (![X24 : $i, X25 : $i]:
% 17.00/17.21         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 17.00/17.21           = (k3_xboole_0 @ X24 @ X25))),
% 17.00/17.21      inference('cnf', [status(esa)], [t48_xboole_1])).
% 17.00/17.21  thf('61', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.00/17.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 17.00/17.21  thf('62', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 17.00/17.21      inference('sup-', [status(thm)], ['45', '46'])).
% 17.00/17.21  thf('63', plain,
% 17.00/17.21      (((u1_struct_0 @ sk_A)
% 17.00/17.21         = (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B))),
% 17.00/17.21      inference('demod', [status(thm)], ['41', '42', '43', '44', '47'])).
% 17.00/17.21  thf('64', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.00/17.21          | (r1_tarski @ sk_B @ X0)
% 17.00/17.21          | ~ (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 17.00/17.21               (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 17.00/17.21      inference('demod', [status(thm)], ['58', '59', '60', '61', '62', '63'])).
% 17.00/17.21  thf('65', plain,
% 17.00/17.21      ((~ (r1_tarski @ 
% 17.00/17.21           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 17.00/17.21           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 17.00/17.21        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 17.00/17.21        | ~ (m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 17.00/17.21             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.00/17.21      inference('sup-', [status(thm)], ['29', '64'])).
% 17.00/17.21  thf('66', plain,
% 17.00/17.21      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 17.00/17.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('demod', [status(thm)], ['25', '26'])).
% 17.00/17.21  thf('67', plain,
% 17.00/17.21      ((~ (r1_tarski @ 
% 17.00/17.21           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 17.00/17.21           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 17.00/17.21        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 17.00/17.21      inference('demod', [status(thm)], ['65', '66'])).
% 17.00/17.21  thf('68', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 17.00/17.21      inference('simplify', [status(thm)], ['35'])).
% 17.00/17.21  thf('69', plain,
% 17.00/17.21      (![X11 : $i, X12 : $i]:
% 17.00/17.21         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 17.00/17.21      inference('cnf', [status(esa)], [t28_xboole_1])).
% 17.00/17.21  thf('70', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 17.00/17.21      inference('sup-', [status(thm)], ['68', '69'])).
% 17.00/17.21  thf('71', plain,
% 17.00/17.21      (![X24 : $i, X25 : $i]:
% 17.00/17.21         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 17.00/17.21           = (k3_xboole_0 @ X24 @ X25))),
% 17.00/17.21      inference('cnf', [status(esa)], [t48_xboole_1])).
% 17.00/17.21  thf('72', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 17.00/17.21      inference('sup-', [status(thm)], ['30', '31'])).
% 17.00/17.21  thf('73', plain,
% 17.00/17.21      (![X5 : $i, X6 : $i, X7 : $i]:
% 17.00/17.21         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 17.00/17.21      inference('cnf', [status(esa)], [t10_xboole_1])).
% 17.00/17.21  thf('74', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['72', '73'])).
% 17.00/17.21  thf(t43_xboole_1, axiom,
% 17.00/17.21    (![A:$i,B:$i,C:$i]:
% 17.00/17.21     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 17.00/17.21       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 17.00/17.21  thf('75', plain,
% 17.00/17.21      (![X19 : $i, X20 : $i, X21 : $i]:
% 17.00/17.21         ((r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 17.00/17.21          | ~ (r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 17.00/17.21      inference('cnf', [status(esa)], [t43_xboole_1])).
% 17.00/17.21  thf('76', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 17.00/17.21      inference('sup-', [status(thm)], ['74', '75'])).
% 17.00/17.21  thf('77', plain,
% 17.00/17.21      (![X40 : $i, X42 : $i]:
% 17.00/17.21         ((m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X42)) | ~ (r1_tarski @ X40 @ X42))),
% 17.00/17.21      inference('cnf', [status(esa)], [t3_subset])).
% 17.00/17.21  thf('78', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 17.00/17.21          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['76', '77'])).
% 17.00/17.21  thf('79', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 17.00/17.21          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('sup+', [status(thm)], ['71', '78'])).
% 17.00/17.21  thf(dt_k3_subset_1, axiom,
% 17.00/17.21    (![A:$i,B:$i]:
% 17.00/17.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 17.00/17.21       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 17.00/17.21  thf('80', plain,
% 17.00/17.21      (![X30 : $i, X31 : $i]:
% 17.00/17.21         ((m1_subset_1 @ (k3_subset_1 @ X30 @ X31) @ (k1_zfmisc_1 @ X30))
% 17.00/17.21          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 17.00/17.21      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 17.00/17.21  thf('81', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         (m1_subset_1 @ 
% 17.00/17.21          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 17.00/17.21          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['79', '80'])).
% 17.00/17.21  thf(d1_tops_1, axiom,
% 17.00/17.21    (![A:$i]:
% 17.00/17.21     ( ( l1_pre_topc @ A ) =>
% 17.00/17.21       ( ![B:$i]:
% 17.00/17.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.00/17.21           ( ( k1_tops_1 @ A @ B ) =
% 17.00/17.21             ( k3_subset_1 @
% 17.00/17.21               ( u1_struct_0 @ A ) @ 
% 17.00/17.21               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 17.00/17.21  thf('82', plain,
% 17.00/17.21      (![X45 : $i, X46 : $i]:
% 17.00/17.21         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 17.00/17.21          | ((k1_tops_1 @ X46 @ X45)
% 17.00/17.21              = (k3_subset_1 @ (u1_struct_0 @ X46) @ 
% 17.00/17.21                 (k2_pre_topc @ X46 @ (k3_subset_1 @ (u1_struct_0 @ X46) @ X45))))
% 17.00/17.21          | ~ (l1_pre_topc @ X46))),
% 17.00/17.21      inference('cnf', [status(esa)], [d1_tops_1])).
% 17.00/17.21  thf('83', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         (~ (l1_pre_topc @ sk_A)
% 17.00/17.21          | ((k1_tops_1 @ sk_A @ 
% 17.00/17.21              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0)))
% 17.00/17.21              = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.00/17.21                 (k2_pre_topc @ sk_A @ 
% 17.00/17.21                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.00/17.21                   (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.00/17.21                    (k3_xboole_0 @ sk_B @ X0)))))))),
% 17.00/17.21      inference('sup-', [status(thm)], ['81', '82'])).
% 17.00/17.21  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf('85', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         ((k1_tops_1 @ sk_A @ 
% 17.00/17.21           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0)))
% 17.00/17.21           = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.00/17.21              (k2_pre_topc @ sk_A @ 
% 17.00/17.21               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.00/17.21                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))))))),
% 17.00/17.21      inference('demod', [status(thm)], ['83', '84'])).
% 17.00/17.21  thf('86', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 17.00/17.21          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('sup+', [status(thm)], ['71', '78'])).
% 17.00/17.21  thf('87', plain,
% 17.00/17.21      (![X28 : $i, X29 : $i]:
% 17.00/17.21         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 17.00/17.21          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 17.00/17.21      inference('cnf', [status(esa)], [d5_subset_1])).
% 17.00/17.21  thf('88', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))
% 17.00/17.21           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['86', '87'])).
% 17.00/17.21  thf('89', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))
% 17.00/17.21           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['86', '87'])).
% 17.00/17.21  thf('90', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]:
% 17.00/17.21         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 17.00/17.21      inference('sup-', [status(thm)], ['18', '19'])).
% 17.00/17.21  thf('91', plain,
% 17.00/17.21      (![X28 : $i, X29 : $i]:
% 17.00/17.21         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 17.00/17.21          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 17.00/17.21      inference('cnf', [status(esa)], [d5_subset_1])).
% 17.00/17.21  thf('92', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]:
% 17.00/17.21         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 17.00/17.21           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['90', '91'])).
% 17.00/17.21  thf('93', plain,
% 17.00/17.21      (![X24 : $i, X25 : $i]:
% 17.00/17.21         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 17.00/17.21           = (k3_xboole_0 @ X24 @ X25))),
% 17.00/17.21      inference('cnf', [status(esa)], [t48_xboole_1])).
% 17.00/17.21  thf('94', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]:
% 17.00/17.21         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 17.00/17.21           = (k3_xboole_0 @ X0 @ X1))),
% 17.00/17.21      inference('demod', [status(thm)], ['92', '93'])).
% 17.00/17.21  thf('95', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.00/17.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 17.00/17.21  thf('96', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.00/17.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 17.00/17.21  thf('97', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 17.00/17.21          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('sup+', [status(thm)], ['71', '78'])).
% 17.00/17.21  thf('98', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 17.00/17.21          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('sup+', [status(thm)], ['96', '97'])).
% 17.00/17.21  thf(involutiveness_k3_subset_1, axiom,
% 17.00/17.21    (![A:$i,B:$i]:
% 17.00/17.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 17.00/17.21       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 17.00/17.21  thf('99', plain,
% 17.00/17.21      (![X32 : $i, X33 : $i]:
% 17.00/17.21         (((k3_subset_1 @ X33 @ (k3_subset_1 @ X33 @ X32)) = (X32))
% 17.00/17.21          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 17.00/17.21      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 17.00/17.21  thf('100', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.00/17.21           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B)))
% 17.00/17.21           = (k3_xboole_0 @ X0 @ sk_B))),
% 17.00/17.21      inference('sup-', [status(thm)], ['98', '99'])).
% 17.00/17.21  thf('101', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 17.00/17.21          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('sup+', [status(thm)], ['96', '97'])).
% 17.00/17.21  thf('102', plain,
% 17.00/17.21      (![X28 : $i, X29 : $i]:
% 17.00/17.21         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 17.00/17.21          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 17.00/17.21      inference('cnf', [status(esa)], [d5_subset_1])).
% 17.00/17.21  thf('103', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 17.00/17.21           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['101', '102'])).
% 17.00/17.21  thf('104', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]:
% 17.00/17.21         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 17.00/17.21           = (k3_xboole_0 @ X0 @ X1))),
% 17.00/17.21      inference('demod', [status(thm)], ['92', '93'])).
% 17.00/17.21  thf('105', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         ((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 17.00/17.21           = (k3_xboole_0 @ X0 @ sk_B))),
% 17.00/17.21      inference('demod', [status(thm)], ['100', '103', '104'])).
% 17.00/17.21  thf('106', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         ((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))
% 17.00/17.21           = (k3_xboole_0 @ X0 @ sk_B))),
% 17.00/17.21      inference('sup+', [status(thm)], ['95', '105'])).
% 17.00/17.21  thf('107', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         ((k1_tops_1 @ sk_A @ 
% 17.00/17.21           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0)))
% 17.00/17.21           = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 17.00/17.21              (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))))),
% 17.00/17.21      inference('demod', [status(thm)], ['85', '88', '89', '94', '106'])).
% 17.00/17.21  thf('108', plain,
% 17.00/17.21      (((k1_tops_1 @ sk_A @ 
% 17.00/17.21         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_B)))
% 17.00/17.21         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 17.00/17.21      inference('sup+', [status(thm)], ['70', '107'])).
% 17.00/17.21  thf('109', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 17.00/17.21      inference('sup-', [status(thm)], ['68', '69'])).
% 17.00/17.21  thf('110', plain,
% 17.00/17.21      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 17.00/17.21         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['27', '28'])).
% 17.00/17.21  thf('111', plain,
% 17.00/17.21      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 17.00/17.21         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 17.00/17.21      inference('demod', [status(thm)], ['108', '109', '110'])).
% 17.00/17.21  thf('112', plain,
% 17.00/17.21      ((~ (r1_tarski @ 
% 17.00/17.21           (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 17.00/17.21           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 17.00/17.21        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 17.00/17.21      inference('demod', [status(thm)], ['67', '111'])).
% 17.00/17.21  thf('113', plain,
% 17.00/17.21      ((~ (l1_pre_topc @ sk_A)
% 17.00/17.21        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['22', '112'])).
% 17.00/17.21  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf('115', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 17.00/17.21      inference('demod', [status(thm)], ['113', '114'])).
% 17.00/17.21  thf('116', plain,
% 17.00/17.21      (![X11 : $i, X12 : $i]:
% 17.00/17.21         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 17.00/17.21      inference('cnf', [status(esa)], [t28_xboole_1])).
% 17.00/17.21  thf('117', plain,
% 17.00/17.21      (((k3_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 17.00/17.21      inference('sup-', [status(thm)], ['115', '116'])).
% 17.00/17.21  thf('118', plain,
% 17.00/17.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf(t72_tops_1, axiom,
% 17.00/17.21    (![A:$i]:
% 17.00/17.21     ( ( l1_pre_topc @ A ) =>
% 17.00/17.21       ( ![B:$i]:
% 17.00/17.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.00/17.21           ( r1_tarski @
% 17.00/17.21             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 17.00/17.21             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 17.00/17.21  thf('119', plain,
% 17.00/17.21      (![X55 : $i, X56 : $i]:
% 17.00/17.21         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 17.00/17.21          | (r1_tarski @ (k2_tops_1 @ X56 @ (k2_pre_topc @ X56 @ X55)) @ 
% 17.00/17.21             (k2_tops_1 @ X56 @ X55))
% 17.00/17.21          | ~ (l1_pre_topc @ X56))),
% 17.00/17.21      inference('cnf', [status(esa)], [t72_tops_1])).
% 17.00/17.21  thf('120', plain,
% 17.00/17.21      ((~ (l1_pre_topc @ sk_A)
% 17.00/17.21        | (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 17.00/17.21           (k2_tops_1 @ sk_A @ sk_B)))),
% 17.00/17.21      inference('sup-', [status(thm)], ['118', '119'])).
% 17.00/17.21  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf('122', plain,
% 17.00/17.21      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 17.00/17.21        (k2_tops_1 @ sk_A @ sk_B))),
% 17.00/17.21      inference('demod', [status(thm)], ['120', '121'])).
% 17.00/17.21  thf('123', plain,
% 17.00/17.21      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 17.00/17.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('demod', [status(thm)], ['25', '26'])).
% 17.00/17.21  thf('124', plain,
% 17.00/17.21      (![X57 : $i, X58 : $i]:
% 17.00/17.21         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 17.00/17.21          | ~ (v2_tops_1 @ X57 @ X58)
% 17.00/17.21          | (r1_tarski @ X57 @ (k2_tops_1 @ X58 @ X57))
% 17.00/17.21          | ~ (l1_pre_topc @ X58))),
% 17.00/17.21      inference('cnf', [status(esa)], [t88_tops_1])).
% 17.00/17.21  thf('125', plain,
% 17.00/17.21      ((~ (l1_pre_topc @ sk_A)
% 17.00/17.21        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 17.00/17.21           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 17.00/17.21        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 17.00/17.21      inference('sup-', [status(thm)], ['123', '124'])).
% 17.00/17.21  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf('127', plain,
% 17.00/17.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf(d5_tops_1, axiom,
% 17.00/17.21    (![A:$i]:
% 17.00/17.21     ( ( l1_pre_topc @ A ) =>
% 17.00/17.21       ( ![B:$i]:
% 17.00/17.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.00/17.21           ( ( v3_tops_1 @ B @ A ) <=>
% 17.00/17.21             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 17.00/17.21  thf('128', plain,
% 17.00/17.21      (![X49 : $i, X50 : $i]:
% 17.00/17.21         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 17.00/17.21          | ~ (v3_tops_1 @ X49 @ X50)
% 17.00/17.21          | (v2_tops_1 @ (k2_pre_topc @ X50 @ X49) @ X50)
% 17.00/17.21          | ~ (l1_pre_topc @ X50))),
% 17.00/17.21      inference('cnf', [status(esa)], [d5_tops_1])).
% 17.00/17.21  thf('129', plain,
% 17.00/17.21      ((~ (l1_pre_topc @ sk_A)
% 17.00/17.21        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 17.00/17.21        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 17.00/17.21      inference('sup-', [status(thm)], ['127', '128'])).
% 17.00/17.21  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf('131', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 17.00/17.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.00/17.21  thf('132', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 17.00/17.21      inference('demod', [status(thm)], ['129', '130', '131'])).
% 17.00/17.21  thf('133', plain,
% 17.00/17.21      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 17.00/17.21        (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 17.00/17.21      inference('demod', [status(thm)], ['125', '126', '132'])).
% 17.00/17.21  thf(t1_xboole_1, axiom,
% 17.00/17.21    (![A:$i,B:$i,C:$i]:
% 17.00/17.21     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 17.00/17.21       ( r1_tarski @ A @ C ) ))).
% 17.00/17.21  thf('134', plain,
% 17.00/17.21      (![X8 : $i, X9 : $i, X10 : $i]:
% 17.00/17.21         (~ (r1_tarski @ X8 @ X9)
% 17.00/17.21          | ~ (r1_tarski @ X9 @ X10)
% 17.00/17.21          | (r1_tarski @ X8 @ X10))),
% 17.00/17.21      inference('cnf', [status(esa)], [t1_xboole_1])).
% 17.00/17.21  thf('135', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 17.00/17.21          | ~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 17.00/17.21               X0))),
% 17.00/17.21      inference('sup-', [status(thm)], ['133', '134'])).
% 17.00/17.21  thf('136', plain,
% 17.00/17.21      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 17.00/17.21      inference('sup-', [status(thm)], ['122', '135'])).
% 17.00/17.21  thf('137', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 17.00/17.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 17.00/17.21  thf('138', plain,
% 17.00/17.21      (![X24 : $i, X25 : $i]:
% 17.00/17.21         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 17.00/17.21           = (k3_xboole_0 @ X24 @ X25))),
% 17.00/17.21      inference('cnf', [status(esa)], [t48_xboole_1])).
% 17.00/17.21  thf('139', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]:
% 17.00/17.21         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 17.00/17.21      inference('sup-', [status(thm)], ['18', '19'])).
% 17.00/17.21  thf('140', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]:
% 17.00/17.21         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 17.00/17.21      inference('sup+', [status(thm)], ['138', '139'])).
% 17.00/17.21  thf('141', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]:
% 17.00/17.21         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 17.00/17.21      inference('sup+', [status(thm)], ['137', '140'])).
% 17.00/17.21  thf('142', plain,
% 17.00/17.21      (![X40 : $i, X41 : $i]:
% 17.00/17.21         ((r1_tarski @ X40 @ X41) | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 17.00/17.21      inference('cnf', [status(esa)], [t3_subset])).
% 17.00/17.21  thf('143', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 17.00/17.21      inference('sup-', [status(thm)], ['141', '142'])).
% 17.00/17.21  thf('144', plain,
% 17.00/17.21      (![X8 : $i, X9 : $i, X10 : $i]:
% 17.00/17.21         (~ (r1_tarski @ X8 @ X9)
% 17.00/17.21          | ~ (r1_tarski @ X9 @ X10)
% 17.00/17.21          | (r1_tarski @ X8 @ X10))),
% 17.00/17.21      inference('cnf', [status(esa)], [t1_xboole_1])).
% 17.00/17.21  thf('145', plain,
% 17.00/17.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.00/17.21         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 17.00/17.21      inference('sup-', [status(thm)], ['143', '144'])).
% 17.00/17.21  thf('146', plain,
% 17.00/17.21      (![X0 : $i]:
% 17.00/17.21         (r1_tarski @ (k3_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 17.00/17.21          (k2_tops_1 @ sk_A @ sk_B))),
% 17.00/17.21      inference('sup-', [status(thm)], ['136', '145'])).
% 17.00/17.21  thf('147', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 17.00/17.21      inference('sup+', [status(thm)], ['117', '146'])).
% 17.00/17.21  thf('148', plain, ($false), inference('demod', [status(thm)], ['17', '147'])).
% 17.00/17.21  
% 17.00/17.21  % SZS output end Refutation
% 17.00/17.21  
% 17.00/17.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
