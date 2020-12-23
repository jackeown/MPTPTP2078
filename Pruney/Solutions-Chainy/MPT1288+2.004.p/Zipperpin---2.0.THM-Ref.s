%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pt5Ed8j8kT

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:58 EST 2020

% Result     : Theorem 3.71s
% Output     : Refutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 320 expanded)
%              Number of leaves         :   33 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          : 1463 (4051 expanded)
%              Number of equality atoms :   34 ( 142 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t110_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
           => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) )
              = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_tops_1 @ B @ A )
             => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) )
                = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t110_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r1_tarski @ X24 @ X26 )
      | ( r1_tarski @ ( k1_tops_1 @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( r1_tarski @ X8 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('27',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('34',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_tops_1 @ X27 @ X28 )
      | ( ( k1_tops_1 @ X28 @ X27 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_tops_1 @ X10 @ X11 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X11 @ X10 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ sk_A )
    | ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ sk_A )
    | ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t96_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) )).

thf('44',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v3_tops_1 @ ( k2_tops_1 @ X30 @ X29 ) @ X30 )
      | ~ ( v4_pre_topc @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t96_tops_1])).

thf('45',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('50',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( ( k2_pre_topc @ X6 @ ( k2_pre_topc @ X6 @ X7 ) )
        = ( k2_pre_topc @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('53',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['50','55','56','57'])).

thf('59',plain,(
    v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['45','46','47','58'])).

thf('60',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['42','59'])).

thf('61',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','60'])).

thf('62',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('63',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_tops_1 @ X21 @ X20 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ X20 ) @ ( k1_tops_1 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('67',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r1_tarski @ X24 @ X26 )
      | ( r1_tarski @ ( k1_tops_1 @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( r1_tarski @ X8 @ ( k2_pre_topc @ X9 @ X8 ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','79'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('81',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('82',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
          <=> ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B )
              & ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('84',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_tops_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_tops_1 @ X13 @ ( k2_pre_topc @ X13 @ X12 ) ) @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('90',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('91',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r1_tarski @ X24 @ X26 )
      | ( r1_tarski @ ( k1_tops_1 @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('98',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k1_tops_1 @ X22 @ ( k1_tops_1 @ X22 @ X23 ) )
        = ( k1_tops_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('99',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96','101'])).

thf('103',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['88','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['82','105'])).

thf('107',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_tops_1 @ X21 @ X20 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ X20 ) @ ( k1_tops_1 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('110',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['107','112'])).

thf('114',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','113'])).

thf('115',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['20','114'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('116',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('117',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pt5Ed8j8kT
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.71/3.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.71/3.90  % Solved by: fo/fo7.sh
% 3.71/3.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.71/3.90  % done 2964 iterations in 3.443s
% 3.71/3.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.71/3.90  % SZS output start Refutation
% 3.71/3.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.71/3.90  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.71/3.90  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 3.71/3.90  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.71/3.90  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.71/3.90  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 3.71/3.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.71/3.90  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.71/3.90  thf(sk_B_type, type, sk_B: $i).
% 3.71/3.90  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.71/3.90  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 3.71/3.90  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 3.71/3.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.71/3.90  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.71/3.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.71/3.90  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 3.71/3.90  thf(sk_A_type, type, sk_A: $i).
% 3.71/3.90  thf(t110_tops_1, conjecture,
% 3.71/3.90    (![A:$i]:
% 3.71/3.90     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.71/3.90       ( ![B:$i]:
% 3.71/3.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.71/3.90           ( ( v4_tops_1 @ B @ A ) =>
% 3.71/3.90             ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 3.71/3.90  thf(zf_stmt_0, negated_conjecture,
% 3.71/3.90    (~( ![A:$i]:
% 3.71/3.90        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.71/3.90          ( ![B:$i]:
% 3.71/3.90            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.71/3.90              ( ( v4_tops_1 @ B @ A ) =>
% 3.71/3.90                ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 3.71/3.90    inference('cnf.neg', [status(esa)], [t110_tops_1])).
% 3.71/3.90  thf('0', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf(dt_k2_tops_1, axiom,
% 3.71/3.90    (![A:$i,B:$i]:
% 3.71/3.90     ( ( ( l1_pre_topc @ A ) & 
% 3.71/3.90         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.71/3.90       ( m1_subset_1 @
% 3.71/3.90         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.71/3.90  thf('1', plain,
% 3.71/3.90      (![X16 : $i, X17 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ X16)
% 3.71/3.90          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 3.71/3.90          | (m1_subset_1 @ (k2_tops_1 @ X16 @ X17) @ 
% 3.71/3.90             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 3.71/3.90      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 3.71/3.90  thf('2', plain,
% 3.71/3.90      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.71/3.90         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.71/3.90        | ~ (l1_pre_topc @ sk_A))),
% 3.71/3.90      inference('sup-', [status(thm)], ['0', '1'])).
% 3.71/3.90  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('4', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.71/3.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('demod', [status(thm)], ['2', '3'])).
% 3.71/3.90  thf(dt_k2_pre_topc, axiom,
% 3.71/3.90    (![A:$i,B:$i]:
% 3.71/3.90     ( ( ( l1_pre_topc @ A ) & 
% 3.71/3.90         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.71/3.90       ( m1_subset_1 @
% 3.71/3.90         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.71/3.90  thf('5', plain,
% 3.71/3.90      (![X4 : $i, X5 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ X4)
% 3.71/3.90          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 3.71/3.90          | (m1_subset_1 @ (k2_pre_topc @ X4 @ X5) @ 
% 3.71/3.90             (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 3.71/3.90      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 3.71/3.90  thf('6', plain,
% 3.71/3.90      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 3.71/3.90         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.71/3.90        | ~ (l1_pre_topc @ sk_A))),
% 3.71/3.90      inference('sup-', [status(thm)], ['4', '5'])).
% 3.71/3.90  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('8', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 3.71/3.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('demod', [status(thm)], ['6', '7'])).
% 3.71/3.90  thf('9', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.71/3.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('demod', [status(thm)], ['2', '3'])).
% 3.71/3.90  thf(t48_tops_1, axiom,
% 3.71/3.90    (![A:$i]:
% 3.71/3.90     ( ( l1_pre_topc @ A ) =>
% 3.71/3.90       ( ![B:$i]:
% 3.71/3.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.71/3.90           ( ![C:$i]:
% 3.71/3.90             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.71/3.90               ( ( r1_tarski @ B @ C ) =>
% 3.71/3.90                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.71/3.90  thf('10', plain,
% 3.71/3.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 3.71/3.90          | ~ (r1_tarski @ X24 @ X26)
% 3.71/3.90          | (r1_tarski @ (k1_tops_1 @ X25 @ X24) @ (k1_tops_1 @ X25 @ X26))
% 3.71/3.90          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 3.71/3.90          | ~ (l1_pre_topc @ X25))),
% 3.71/3.90      inference('cnf', [status(esa)], [t48_tops_1])).
% 3.71/3.90  thf('11', plain,
% 3.71/3.90      (![X0 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ sk_A)
% 3.71/3.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.71/3.90          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 3.71/3.90             (k1_tops_1 @ sk_A @ X0))
% 3.71/3.90          | ~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0))),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('13', plain,
% 3.71/3.90      (![X0 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.71/3.90          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 3.71/3.90             (k1_tops_1 @ sk_A @ X0))
% 3.71/3.90          | ~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0))),
% 3.71/3.90      inference('demod', [status(thm)], ['11', '12'])).
% 3.71/3.90  thf('14', plain,
% 3.71/3.90      ((~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.71/3.90           (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 3.71/3.90        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 3.71/3.90           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 3.71/3.90      inference('sup-', [status(thm)], ['8', '13'])).
% 3.71/3.90  thf('15', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.71/3.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('demod', [status(thm)], ['2', '3'])).
% 3.71/3.90  thf(t48_pre_topc, axiom,
% 3.71/3.90    (![A:$i]:
% 3.71/3.90     ( ( l1_pre_topc @ A ) =>
% 3.71/3.90       ( ![B:$i]:
% 3.71/3.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.71/3.90           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 3.71/3.90  thf('16', plain,
% 3.71/3.90      (![X8 : $i, X9 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 3.71/3.90          | (r1_tarski @ X8 @ (k2_pre_topc @ X9 @ X8))
% 3.71/3.90          | ~ (l1_pre_topc @ X9))),
% 3.71/3.90      inference('cnf', [status(esa)], [t48_pre_topc])).
% 3.71/3.90  thf('17', plain,
% 3.71/3.90      ((~ (l1_pre_topc @ sk_A)
% 3.71/3.90        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.71/3.90           (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 3.71/3.90      inference('sup-', [status(thm)], ['15', '16'])).
% 3.71/3.90  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('19', plain,
% 3.71/3.90      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.71/3.90        (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.71/3.90      inference('demod', [status(thm)], ['17', '18'])).
% 3.71/3.90  thf('20', plain,
% 3.71/3.90      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 3.71/3.90        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['14', '19'])).
% 3.71/3.90  thf('21', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('22', plain,
% 3.71/3.90      (![X4 : $i, X5 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ X4)
% 3.71/3.90          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 3.71/3.90          | (m1_subset_1 @ (k2_pre_topc @ X4 @ X5) @ 
% 3.71/3.90             (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 3.71/3.90      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 3.71/3.90  thf('23', plain,
% 3.71/3.90      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.71/3.90         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.71/3.90        | ~ (l1_pre_topc @ sk_A))),
% 3.71/3.90      inference('sup-', [status(thm)], ['21', '22'])).
% 3.71/3.90  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('25', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.71/3.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('demod', [status(thm)], ['23', '24'])).
% 3.71/3.90  thf('26', plain,
% 3.71/3.90      (![X16 : $i, X17 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ X16)
% 3.71/3.90          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 3.71/3.90          | (m1_subset_1 @ (k2_tops_1 @ X16 @ X17) @ 
% 3.71/3.90             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 3.71/3.90      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 3.71/3.90  thf('27', plain,
% 3.71/3.90      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.90         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.71/3.90        | ~ (l1_pre_topc @ sk_A))),
% 3.71/3.90      inference('sup-', [status(thm)], ['25', '26'])).
% 3.71/3.90  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('29', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('demod', [status(thm)], ['27', '28'])).
% 3.71/3.90  thf('30', plain,
% 3.71/3.90      (![X4 : $i, X5 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ X4)
% 3.71/3.90          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 3.71/3.90          | (m1_subset_1 @ (k2_pre_topc @ X4 @ X5) @ 
% 3.71/3.90             (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 3.71/3.90      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 3.71/3.90  thf('31', plain,
% 3.71/3.90      (((m1_subset_1 @ 
% 3.71/3.90         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 3.71/3.90         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.71/3.90        | ~ (l1_pre_topc @ sk_A))),
% 3.71/3.90      inference('sup-', [status(thm)], ['29', '30'])).
% 3.71/3.90  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('33', plain,
% 3.71/3.90      ((m1_subset_1 @ 
% 3.71/3.90        (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 3.71/3.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('demod', [status(thm)], ['31', '32'])).
% 3.71/3.90  thf(t84_tops_1, axiom,
% 3.71/3.90    (![A:$i]:
% 3.71/3.90     ( ( l1_pre_topc @ A ) =>
% 3.71/3.90       ( ![B:$i]:
% 3.71/3.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.71/3.90           ( ( v2_tops_1 @ B @ A ) <=>
% 3.71/3.90             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 3.71/3.90  thf('34', plain,
% 3.71/3.90      (![X27 : $i, X28 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 3.71/3.90          | ~ (v2_tops_1 @ X27 @ X28)
% 3.71/3.90          | ((k1_tops_1 @ X28 @ X27) = (k1_xboole_0))
% 3.71/3.90          | ~ (l1_pre_topc @ X28))),
% 3.71/3.90      inference('cnf', [status(esa)], [t84_tops_1])).
% 3.71/3.90  thf('35', plain,
% 3.71/3.90      ((~ (l1_pre_topc @ sk_A)
% 3.71/3.90        | ((k1_tops_1 @ sk_A @ 
% 3.71/3.90            (k2_pre_topc @ sk_A @ 
% 3.71/3.90             (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 3.71/3.90            = (k1_xboole_0))
% 3.71/3.90        | ~ (v2_tops_1 @ 
% 3.71/3.90             (k2_pre_topc @ sk_A @ 
% 3.71/3.90              (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 3.71/3.90             sk_A))),
% 3.71/3.90      inference('sup-', [status(thm)], ['33', '34'])).
% 3.71/3.90  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('37', plain,
% 3.71/3.90      ((((k1_tops_1 @ sk_A @ 
% 3.71/3.90          (k2_pre_topc @ sk_A @ 
% 3.71/3.90           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 3.71/3.90          = (k1_xboole_0))
% 3.71/3.90        | ~ (v2_tops_1 @ 
% 3.71/3.90             (k2_pre_topc @ sk_A @ 
% 3.71/3.90              (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 3.71/3.90             sk_A))),
% 3.71/3.90      inference('demod', [status(thm)], ['35', '36'])).
% 3.71/3.90  thf('38', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('demod', [status(thm)], ['27', '28'])).
% 3.71/3.90  thf(d5_tops_1, axiom,
% 3.71/3.90    (![A:$i]:
% 3.71/3.90     ( ( l1_pre_topc @ A ) =>
% 3.71/3.90       ( ![B:$i]:
% 3.71/3.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.71/3.90           ( ( v3_tops_1 @ B @ A ) <=>
% 3.71/3.90             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 3.71/3.90  thf('39', plain,
% 3.71/3.90      (![X10 : $i, X11 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 3.71/3.90          | ~ (v3_tops_1 @ X10 @ X11)
% 3.71/3.90          | (v2_tops_1 @ (k2_pre_topc @ X11 @ X10) @ X11)
% 3.71/3.90          | ~ (l1_pre_topc @ X11))),
% 3.71/3.90      inference('cnf', [status(esa)], [d5_tops_1])).
% 3.71/3.90  thf('40', plain,
% 3.71/3.90      ((~ (l1_pre_topc @ sk_A)
% 3.71/3.90        | (v2_tops_1 @ 
% 3.71/3.90           (k2_pre_topc @ sk_A @ 
% 3.71/3.90            (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 3.71/3.90           sk_A)
% 3.71/3.90        | ~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.90             sk_A))),
% 3.71/3.90      inference('sup-', [status(thm)], ['38', '39'])).
% 3.71/3.90  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('42', plain,
% 3.71/3.90      (((v2_tops_1 @ 
% 3.71/3.90         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 3.71/3.90         sk_A)
% 3.71/3.90        | ~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.90             sk_A))),
% 3.71/3.90      inference('demod', [status(thm)], ['40', '41'])).
% 3.71/3.90  thf('43', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.71/3.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('demod', [status(thm)], ['23', '24'])).
% 3.71/3.90  thf(t96_tops_1, axiom,
% 3.71/3.90    (![A:$i]:
% 3.71/3.90     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.71/3.90       ( ![B:$i]:
% 3.71/3.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.71/3.90           ( ( v4_pre_topc @ B @ A ) =>
% 3.71/3.90             ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ))).
% 3.71/3.90  thf('44', plain,
% 3.71/3.90      (![X29 : $i, X30 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 3.71/3.90          | (v3_tops_1 @ (k2_tops_1 @ X30 @ X29) @ X30)
% 3.71/3.90          | ~ (v4_pre_topc @ X29 @ X30)
% 3.71/3.90          | ~ (l1_pre_topc @ X30)
% 3.71/3.90          | ~ (v2_pre_topc @ X30))),
% 3.71/3.90      inference('cnf', [status(esa)], [t96_tops_1])).
% 3.71/3.90  thf('45', plain,
% 3.71/3.90      ((~ (v2_pre_topc @ sk_A)
% 3.71/3.90        | ~ (l1_pre_topc @ sk_A)
% 3.71/3.90        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 3.71/3.90        | (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A))),
% 3.71/3.90      inference('sup-', [status(thm)], ['43', '44'])).
% 3.71/3.90  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('48', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.71/3.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('demod', [status(thm)], ['23', '24'])).
% 3.71/3.90  thf(fc1_tops_1, axiom,
% 3.71/3.90    (![A:$i,B:$i]:
% 3.71/3.90     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 3.71/3.90         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.71/3.90       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 3.71/3.90  thf('49', plain,
% 3.71/3.90      (![X18 : $i, X19 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ X18)
% 3.71/3.90          | ~ (v2_pre_topc @ X18)
% 3.71/3.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 3.71/3.90          | (v4_pre_topc @ (k2_pre_topc @ X18 @ X19) @ X18))),
% 3.71/3.90      inference('cnf', [status(esa)], [fc1_tops_1])).
% 3.71/3.90  thf('50', plain,
% 3.71/3.90      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.90         sk_A)
% 3.71/3.90        | ~ (v2_pre_topc @ sk_A)
% 3.71/3.90        | ~ (l1_pre_topc @ sk_A))),
% 3.71/3.90      inference('sup-', [status(thm)], ['48', '49'])).
% 3.71/3.90  thf('51', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf(projectivity_k2_pre_topc, axiom,
% 3.71/3.90    (![A:$i,B:$i]:
% 3.71/3.90     ( ( ( l1_pre_topc @ A ) & 
% 3.71/3.90         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.71/3.90       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 3.71/3.90         ( k2_pre_topc @ A @ B ) ) ))).
% 3.71/3.90  thf('52', plain,
% 3.71/3.90      (![X6 : $i, X7 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ X6)
% 3.71/3.90          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 3.71/3.90          | ((k2_pre_topc @ X6 @ (k2_pre_topc @ X6 @ X7))
% 3.71/3.90              = (k2_pre_topc @ X6 @ X7)))),
% 3.71/3.90      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 3.71/3.90  thf('53', plain,
% 3.71/3.90      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 3.71/3.90          = (k2_pre_topc @ sk_A @ sk_B))
% 3.71/3.90        | ~ (l1_pre_topc @ sk_A))),
% 3.71/3.90      inference('sup-', [status(thm)], ['51', '52'])).
% 3.71/3.90  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('55', plain,
% 3.71/3.90      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 3.71/3.90         = (k2_pre_topc @ sk_A @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['53', '54'])).
% 3.71/3.90  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('58', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 3.71/3.90      inference('demod', [status(thm)], ['50', '55', '56', '57'])).
% 3.71/3.90  thf('59', plain,
% 3.71/3.90      ((v3_tops_1 @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_A)),
% 3.71/3.90      inference('demod', [status(thm)], ['45', '46', '47', '58'])).
% 3.71/3.90  thf('60', plain,
% 3.71/3.90      ((v2_tops_1 @ 
% 3.71/3.90        (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 3.71/3.90        sk_A)),
% 3.71/3.90      inference('demod', [status(thm)], ['42', '59'])).
% 3.71/3.90  thf('61', plain,
% 3.71/3.90      (((k1_tops_1 @ sk_A @ 
% 3.71/3.90         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 3.71/3.90         = (k1_xboole_0))),
% 3.71/3.90      inference('demod', [status(thm)], ['37', '60'])).
% 3.71/3.90  thf('62', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.71/3.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('demod', [status(thm)], ['23', '24'])).
% 3.71/3.90  thf(l78_tops_1, axiom,
% 3.71/3.90    (![A:$i]:
% 3.71/3.90     ( ( l1_pre_topc @ A ) =>
% 3.71/3.90       ( ![B:$i]:
% 3.71/3.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.71/3.90           ( ( k2_tops_1 @ A @ B ) =
% 3.71/3.90             ( k7_subset_1 @
% 3.71/3.90               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 3.71/3.90               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.71/3.90  thf('63', plain,
% 3.71/3.90      (![X20 : $i, X21 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 3.71/3.90          | ((k2_tops_1 @ X21 @ X20)
% 3.71/3.90              = (k7_subset_1 @ (u1_struct_0 @ X21) @ 
% 3.71/3.90                 (k2_pre_topc @ X21 @ X20) @ (k1_tops_1 @ X21 @ X20)))
% 3.71/3.90          | ~ (l1_pre_topc @ X21))),
% 3.71/3.90      inference('cnf', [status(esa)], [l78_tops_1])).
% 3.71/3.90  thf('64', plain,
% 3.71/3.90      ((~ (l1_pre_topc @ sk_A)
% 3.71/3.90        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 3.71/3.90            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.71/3.90               (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.90               (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 3.71/3.90      inference('sup-', [status(thm)], ['62', '63'])).
% 3.71/3.90  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('66', plain,
% 3.71/3.90      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 3.71/3.90         = (k2_pre_topc @ sk_A @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['53', '54'])).
% 3.71/3.90  thf('67', plain,
% 3.71/3.90      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 3.71/3.90         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.71/3.90            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['64', '65', '66'])).
% 3.71/3.90  thf('68', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.71/3.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('demod', [status(thm)], ['23', '24'])).
% 3.71/3.90  thf('69', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('70', plain,
% 3.71/3.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 3.71/3.90          | ~ (r1_tarski @ X24 @ X26)
% 3.71/3.90          | (r1_tarski @ (k1_tops_1 @ X25 @ X24) @ (k1_tops_1 @ X25 @ X26))
% 3.71/3.90          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 3.71/3.90          | ~ (l1_pre_topc @ X25))),
% 3.71/3.90      inference('cnf', [status(esa)], [t48_tops_1])).
% 3.71/3.90  thf('71', plain,
% 3.71/3.90      (![X0 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ sk_A)
% 3.71/3.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.71/3.90          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 3.71/3.90          | ~ (r1_tarski @ sk_B @ X0))),
% 3.71/3.90      inference('sup-', [status(thm)], ['69', '70'])).
% 3.71/3.90  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('73', plain,
% 3.71/3.90      (![X0 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.71/3.90          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 3.71/3.90          | ~ (r1_tarski @ sk_B @ X0))),
% 3.71/3.90      inference('demod', [status(thm)], ['71', '72'])).
% 3.71/3.90  thf('74', plain,
% 3.71/3.90      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 3.71/3.90        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.71/3.90           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 3.71/3.90      inference('sup-', [status(thm)], ['68', '73'])).
% 3.71/3.90  thf('75', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('76', plain,
% 3.71/3.90      (![X8 : $i, X9 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 3.71/3.90          | (r1_tarski @ X8 @ (k2_pre_topc @ X9 @ X8))
% 3.71/3.91          | ~ (l1_pre_topc @ X9))),
% 3.71/3.91      inference('cnf', [status(esa)], [t48_pre_topc])).
% 3.71/3.91  thf('77', plain,
% 3.71/3.91      ((~ (l1_pre_topc @ sk_A)
% 3.71/3.91        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 3.71/3.91      inference('sup-', [status(thm)], ['75', '76'])).
% 3.71/3.91  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.91  thf('79', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 3.71/3.91      inference('demod', [status(thm)], ['77', '78'])).
% 3.71/3.91  thf('80', plain,
% 3.71/3.91      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.71/3.91        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 3.71/3.91      inference('demod', [status(thm)], ['74', '79'])).
% 3.71/3.91  thf(d10_xboole_0, axiom,
% 3.71/3.91    (![A:$i,B:$i]:
% 3.71/3.91     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.71/3.91  thf('81', plain,
% 3.71/3.91      (![X0 : $i, X2 : $i]:
% 3.71/3.91         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.71/3.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.71/3.91  thf('82', plain,
% 3.71/3.91      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.91           (k1_tops_1 @ sk_A @ sk_B))
% 3.71/3.91        | ((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 3.71/3.91            = (k1_tops_1 @ sk_A @ sk_B)))),
% 3.71/3.91      inference('sup-', [status(thm)], ['80', '81'])).
% 3.71/3.91  thf('83', plain,
% 3.71/3.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.91  thf(d6_tops_1, axiom,
% 3.71/3.91    (![A:$i]:
% 3.71/3.91     ( ( l1_pre_topc @ A ) =>
% 3.71/3.91       ( ![B:$i]:
% 3.71/3.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.71/3.91           ( ( v4_tops_1 @ B @ A ) <=>
% 3.71/3.91             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 3.71/3.91               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 3.71/3.91  thf('84', plain,
% 3.71/3.91      (![X12 : $i, X13 : $i]:
% 3.71/3.91         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 3.71/3.91          | ~ (v4_tops_1 @ X12 @ X13)
% 3.71/3.91          | (r1_tarski @ (k1_tops_1 @ X13 @ (k2_pre_topc @ X13 @ X12)) @ X12)
% 3.71/3.91          | ~ (l1_pre_topc @ X13))),
% 3.71/3.91      inference('cnf', [status(esa)], [d6_tops_1])).
% 3.71/3.91  thf('85', plain,
% 3.71/3.91      ((~ (l1_pre_topc @ sk_A)
% 3.71/3.91        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)
% 3.71/3.91        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 3.71/3.91      inference('sup-', [status(thm)], ['83', '84'])).
% 3.71/3.91  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.91  thf('87', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 3.71/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.91  thf('88', plain,
% 3.71/3.91      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)),
% 3.71/3.91      inference('demod', [status(thm)], ['85', '86', '87'])).
% 3.71/3.91  thf('89', plain,
% 3.71/3.91      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.71/3.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.91      inference('demod', [status(thm)], ['23', '24'])).
% 3.71/3.91  thf(dt_k1_tops_1, axiom,
% 3.71/3.91    (![A:$i,B:$i]:
% 3.71/3.91     ( ( ( l1_pre_topc @ A ) & 
% 3.71/3.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.71/3.91       ( m1_subset_1 @
% 3.71/3.91         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.71/3.91  thf('90', plain,
% 3.71/3.91      (![X14 : $i, X15 : $i]:
% 3.71/3.91         (~ (l1_pre_topc @ X14)
% 3.71/3.91          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 3.71/3.91          | (m1_subset_1 @ (k1_tops_1 @ X14 @ X15) @ 
% 3.71/3.91             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 3.71/3.91      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 3.71/3.91  thf('91', plain,
% 3.71/3.91      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.91         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.71/3.91        | ~ (l1_pre_topc @ sk_A))),
% 3.71/3.91      inference('sup-', [status(thm)], ['89', '90'])).
% 3.71/3.91  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.91  thf('93', plain,
% 3.71/3.91      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.91      inference('demod', [status(thm)], ['91', '92'])).
% 3.71/3.91  thf('94', plain,
% 3.71/3.91      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.71/3.91         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 3.71/3.91          | ~ (r1_tarski @ X24 @ X26)
% 3.71/3.91          | (r1_tarski @ (k1_tops_1 @ X25 @ X24) @ (k1_tops_1 @ X25 @ X26))
% 3.71/3.91          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 3.71/3.91          | ~ (l1_pre_topc @ X25))),
% 3.71/3.91      inference('cnf', [status(esa)], [t48_tops_1])).
% 3.71/3.91  thf('95', plain,
% 3.71/3.91      (![X0 : $i]:
% 3.71/3.91         (~ (l1_pre_topc @ sk_A)
% 3.71/3.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.71/3.91          | (r1_tarski @ 
% 3.71/3.91             (k1_tops_1 @ sk_A @ 
% 3.71/3.91              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 3.71/3.91             (k1_tops_1 @ sk_A @ X0))
% 3.71/3.91          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.91               X0))),
% 3.71/3.91      inference('sup-', [status(thm)], ['93', '94'])).
% 3.71/3.91  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.91  thf('97', plain,
% 3.71/3.91      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.71/3.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.91      inference('demod', [status(thm)], ['23', '24'])).
% 3.71/3.91  thf(projectivity_k1_tops_1, axiom,
% 3.71/3.91    (![A:$i,B:$i]:
% 3.71/3.91     ( ( ( l1_pre_topc @ A ) & 
% 3.71/3.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.71/3.91       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 3.71/3.91  thf('98', plain,
% 3.71/3.91      (![X22 : $i, X23 : $i]:
% 3.71/3.91         (~ (l1_pre_topc @ X22)
% 3.71/3.91          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 3.71/3.91          | ((k1_tops_1 @ X22 @ (k1_tops_1 @ X22 @ X23))
% 3.71/3.91              = (k1_tops_1 @ X22 @ X23)))),
% 3.71/3.91      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 3.71/3.91  thf('99', plain,
% 3.71/3.91      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 3.71/3.91          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 3.71/3.91        | ~ (l1_pre_topc @ sk_A))),
% 3.71/3.91      inference('sup-', [status(thm)], ['97', '98'])).
% 3.71/3.91  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.91  thf('101', plain,
% 3.71/3.91      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 3.71/3.91         = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 3.71/3.91      inference('demod', [status(thm)], ['99', '100'])).
% 3.71/3.91  thf('102', plain,
% 3.71/3.91      (![X0 : $i]:
% 3.71/3.91         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.71/3.91          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.91             (k1_tops_1 @ sk_A @ X0))
% 3.71/3.91          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.91               X0))),
% 3.71/3.91      inference('demod', [status(thm)], ['95', '96', '101'])).
% 3.71/3.91  thf('103', plain,
% 3.71/3.91      (((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.91         (k1_tops_1 @ sk_A @ sk_B))
% 3.71/3.91        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.71/3.91      inference('sup-', [status(thm)], ['88', '102'])).
% 3.71/3.91  thf('104', plain,
% 3.71/3.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.91  thf('105', plain,
% 3.71/3.91      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 3.71/3.91        (k1_tops_1 @ sk_A @ sk_B))),
% 3.71/3.91      inference('demod', [status(thm)], ['103', '104'])).
% 3.71/3.91  thf('106', plain,
% 3.71/3.91      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 3.71/3.91         = (k1_tops_1 @ sk_A @ sk_B))),
% 3.71/3.91      inference('demod', [status(thm)], ['82', '105'])).
% 3.71/3.91  thf('107', plain,
% 3.71/3.91      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 3.71/3.91         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.71/3.91            (k1_tops_1 @ sk_A @ sk_B)))),
% 3.71/3.91      inference('demod', [status(thm)], ['67', '106'])).
% 3.71/3.91  thf('108', plain,
% 3.71/3.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.71/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.91  thf('109', plain,
% 3.71/3.91      (![X20 : $i, X21 : $i]:
% 3.71/3.91         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 3.71/3.91          | ((k2_tops_1 @ X21 @ X20)
% 3.71/3.91              = (k7_subset_1 @ (u1_struct_0 @ X21) @ 
% 3.71/3.91                 (k2_pre_topc @ X21 @ X20) @ (k1_tops_1 @ X21 @ X20)))
% 3.71/3.91          | ~ (l1_pre_topc @ X21))),
% 3.71/3.91      inference('cnf', [status(esa)], [l78_tops_1])).
% 3.71/3.91  thf('110', plain,
% 3.71/3.91      ((~ (l1_pre_topc @ sk_A)
% 3.71/3.91        | ((k2_tops_1 @ sk_A @ sk_B)
% 3.71/3.91            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.71/3.91               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 3.71/3.91      inference('sup-', [status(thm)], ['108', '109'])).
% 3.71/3.91  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.91  thf('112', plain,
% 3.71/3.91      (((k2_tops_1 @ sk_A @ sk_B)
% 3.71/3.91         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.71/3.91            (k1_tops_1 @ sk_A @ sk_B)))),
% 3.71/3.91      inference('demod', [status(thm)], ['110', '111'])).
% 3.71/3.91  thf('113', plain,
% 3.71/3.91      (((k2_tops_1 @ sk_A @ sk_B)
% 3.71/3.91         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 3.71/3.91      inference('sup+', [status(thm)], ['107', '112'])).
% 3.71/3.91  thf('114', plain,
% 3.71/3.91      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 3.71/3.91         = (k1_xboole_0))),
% 3.71/3.91      inference('demod', [status(thm)], ['61', '113'])).
% 3.71/3.91  thf('115', plain,
% 3.71/3.91      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 3.71/3.91        k1_xboole_0)),
% 3.71/3.91      inference('demod', [status(thm)], ['20', '114'])).
% 3.71/3.91  thf(t3_xboole_1, axiom,
% 3.71/3.91    (![A:$i]:
% 3.71/3.91     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.71/3.91  thf('116', plain,
% 3.71/3.91      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 3.71/3.91      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.71/3.91  thf('117', plain,
% 3.71/3.91      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 3.71/3.91      inference('sup-', [status(thm)], ['115', '116'])).
% 3.71/3.91  thf('118', plain,
% 3.71/3.91      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 3.71/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.91  thf('119', plain, ($false),
% 3.71/3.91      inference('simplify_reflect-', [status(thm)], ['117', '118'])).
% 3.71/3.91  
% 3.71/3.91  % SZS output end Refutation
% 3.71/3.91  
% 3.76/3.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
