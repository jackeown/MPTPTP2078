%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CBljcSYEjm

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:28 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 774 expanded)
%              Number of leaves         :   49 ( 266 expanded)
%              Depth                    :   17
%              Number of atoms          : 1559 (6339 expanded)
%              Number of equality atoms :   72 ( 341 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ~ ( r1_tarski @ X64 @ ( k2_tops_1 @ X65 @ X64 ) )
      | ( v2_tops_1 @ X64 @ X65 )
      | ~ ( l1_pre_topc @ X65 ) ) ),
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
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( v2_tops_1 @ X52 @ X53 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X53 ) @ X52 ) @ X53 )
      | ~ ( l1_pre_topc @ X53 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
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

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('20',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('22',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('24',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('25',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X63 @ ( k2_pre_topc @ X63 @ X62 ) ) @ ( k2_tops_1 @ X63 @ X62 ) )
      | ~ ( l1_pre_topc @ X63 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X28 ) @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('30',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('31',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('48',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('49',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('51',plain,(
    ! [X24: $i] :
      ( ( k1_subset_1 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('52',plain,(
    ! [X37: $i] :
      ( ( k2_subset_1 @ X37 )
      = ( k3_subset_1 @ X37 @ ( k1_subset_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('53',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('54',plain,(
    ! [X37: $i] :
      ( X37
      = ( k3_subset_1 @ X37 @ ( k1_subset_1 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','56'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('58',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('59',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['57','64'])).

thf('66',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['57','64'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('67',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('68',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['66','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('76',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','56'])).

thf('77',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['57','64'])).

thf('79',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('80',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','65','77','78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('82',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( l1_pre_topc @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X50 @ X51 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('83',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('87',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('89',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ~ ( v2_tops_1 @ X64 @ X65 )
      | ( r1_tarski @ X64 @ ( k2_tops_1 @ X65 @ X64 ) )
      | ~ ( l1_pre_topc @ X65 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v2_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v2_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('95',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('96',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('99',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('100',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('101',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('108',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('110',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('112',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('114',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('117',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('118',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('120',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('121',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('122',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ~ ( v3_tops_1 @ X54 @ X55 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X55 @ X54 ) @ X55 )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('123',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','96','97','114','115','116','117','118','119','120','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('129',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( ( k2_pre_topc @ X61 @ X60 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X61 ) @ X60 @ ( k2_tops_1 @ X61 @ X60 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('130',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('134',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( l1_pre_topc @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X56 @ X57 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('135',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('139',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k4_subset_1 @ X32 @ X31 @ X33 )
        = ( k2_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['132','141'])).

thf('143',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','144'])).

thf('146',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['80','147'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['17','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CBljcSYEjm
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:20:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.81/2.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.81/2.00  % Solved by: fo/fo7.sh
% 1.81/2.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.81/2.00  % done 5060 iterations in 1.543s
% 1.81/2.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.81/2.00  % SZS output start Refutation
% 1.81/2.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.81/2.00  thf(sk_A_type, type, sk_A: $i).
% 1.81/2.00  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.81/2.00  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.81/2.00  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.81/2.00  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 1.81/2.00  thf(sk_B_type, type, sk_B: $i).
% 1.81/2.00  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.81/2.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.81/2.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.81/2.00  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.81/2.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.81/2.00  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.81/2.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.81/2.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.81/2.00  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.81/2.00  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 1.81/2.00  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 1.81/2.00  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.81/2.00  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 1.81/2.00  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.81/2.00  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.81/2.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.81/2.00  thf(t91_tops_1, conjecture,
% 1.81/2.00    (![A:$i]:
% 1.81/2.00     ( ( l1_pre_topc @ A ) =>
% 1.81/2.00       ( ![B:$i]:
% 1.81/2.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.81/2.00           ( ( v3_tops_1 @ B @ A ) =>
% 1.81/2.00             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.81/2.00  thf(zf_stmt_0, negated_conjecture,
% 1.81/2.00    (~( ![A:$i]:
% 1.81/2.00        ( ( l1_pre_topc @ A ) =>
% 1.81/2.00          ( ![B:$i]:
% 1.81/2.00            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.81/2.00              ( ( v3_tops_1 @ B @ A ) =>
% 1.81/2.00                ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 1.81/2.00    inference('cnf.neg', [status(esa)], [t91_tops_1])).
% 1.81/2.00  thf('0', plain,
% 1.81/2.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf(t88_tops_1, axiom,
% 1.81/2.00    (![A:$i]:
% 1.81/2.00     ( ( l1_pre_topc @ A ) =>
% 1.81/2.00       ( ![B:$i]:
% 1.81/2.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.81/2.00           ( ( v2_tops_1 @ B @ A ) <=>
% 1.81/2.00             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.81/2.00  thf('1', plain,
% 1.81/2.00      (![X64 : $i, X65 : $i]:
% 1.81/2.00         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 1.81/2.00          | ~ (r1_tarski @ X64 @ (k2_tops_1 @ X65 @ X64))
% 1.81/2.00          | (v2_tops_1 @ X64 @ X65)
% 1.81/2.00          | ~ (l1_pre_topc @ X65))),
% 1.81/2.00      inference('cnf', [status(esa)], [t88_tops_1])).
% 1.81/2.00  thf('2', plain,
% 1.81/2.00      ((~ (l1_pre_topc @ sk_A)
% 1.81/2.00        | (v2_tops_1 @ sk_B @ sk_A)
% 1.81/2.00        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.81/2.00      inference('sup-', [status(thm)], ['0', '1'])).
% 1.81/2.00  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf('4', plain,
% 1.81/2.00      (((v2_tops_1 @ sk_B @ sk_A)
% 1.81/2.00        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.81/2.00      inference('demod', [status(thm)], ['2', '3'])).
% 1.81/2.00  thf('5', plain,
% 1.81/2.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf(d4_tops_1, axiom,
% 1.81/2.00    (![A:$i]:
% 1.81/2.00     ( ( l1_pre_topc @ A ) =>
% 1.81/2.00       ( ![B:$i]:
% 1.81/2.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.81/2.00           ( ( v2_tops_1 @ B @ A ) <=>
% 1.81/2.00             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.81/2.00  thf('6', plain,
% 1.81/2.00      (![X52 : $i, X53 : $i]:
% 1.81/2.00         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 1.81/2.00          | ~ (v2_tops_1 @ X52 @ X53)
% 1.81/2.00          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X53) @ X52) @ X53)
% 1.81/2.00          | ~ (l1_pre_topc @ X53))),
% 1.81/2.00      inference('cnf', [status(esa)], [d4_tops_1])).
% 1.81/2.00  thf('7', plain,
% 1.81/2.00      ((~ (l1_pre_topc @ sk_A)
% 1.81/2.00        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.81/2.00        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.81/2.00      inference('sup-', [status(thm)], ['5', '6'])).
% 1.81/2.00  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf('9', plain,
% 1.81/2.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf(d5_subset_1, axiom,
% 1.81/2.00    (![A:$i,B:$i]:
% 1.81/2.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.81/2.00       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.81/2.00  thf('10', plain,
% 1.81/2.00      (![X26 : $i, X27 : $i]:
% 1.81/2.00         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 1.81/2.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.81/2.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.81/2.00  thf('11', plain,
% 1.81/2.00      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.81/2.00         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.81/2.00      inference('sup-', [status(thm)], ['9', '10'])).
% 1.81/2.00  thf('12', plain,
% 1.81/2.00      (((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.81/2.00        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.81/2.00      inference('demod', [status(thm)], ['7', '8', '11'])).
% 1.81/2.00  thf('13', plain,
% 1.81/2.00      (~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf('14', plain,
% 1.81/2.00      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.81/2.00         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.81/2.00      inference('sup-', [status(thm)], ['9', '10'])).
% 1.81/2.00  thf('15', plain,
% 1.81/2.00      (~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 1.81/2.00      inference('demod', [status(thm)], ['13', '14'])).
% 1.81/2.00  thf('16', plain, (~ (v2_tops_1 @ sk_B @ sk_A)),
% 1.81/2.00      inference('clc', [status(thm)], ['12', '15'])).
% 1.81/2.00  thf('17', plain, (~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 1.81/2.00      inference('clc', [status(thm)], ['4', '16'])).
% 1.81/2.00  thf('18', plain,
% 1.81/2.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf(dt_k3_subset_1, axiom,
% 1.81/2.00    (![A:$i,B:$i]:
% 1.81/2.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.81/2.00       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.81/2.00  thf('19', plain,
% 1.81/2.00      (![X29 : $i, X30 : $i]:
% 1.81/2.00         ((m1_subset_1 @ (k3_subset_1 @ X29 @ X30) @ (k1_zfmisc_1 @ X29))
% 1.81/2.00          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 1.81/2.00      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.81/2.00  thf('20', plain,
% 1.81/2.00      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.81/2.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('sup-', [status(thm)], ['18', '19'])).
% 1.81/2.00  thf('21', plain,
% 1.81/2.00      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.81/2.00         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.81/2.00      inference('sup-', [status(thm)], ['9', '10'])).
% 1.81/2.00  thf('22', plain,
% 1.81/2.00      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.81/2.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('demod', [status(thm)], ['20', '21'])).
% 1.81/2.00  thf('23', plain,
% 1.81/2.00      (![X29 : $i, X30 : $i]:
% 1.81/2.00         ((m1_subset_1 @ (k3_subset_1 @ X29 @ X30) @ (k1_zfmisc_1 @ X29))
% 1.81/2.00          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 1.81/2.00      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.81/2.00  thf('24', plain,
% 1.81/2.00      ((m1_subset_1 @ 
% 1.81/2.00        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.81/2.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('sup-', [status(thm)], ['22', '23'])).
% 1.81/2.00  thf(t72_tops_1, axiom,
% 1.81/2.00    (![A:$i]:
% 1.81/2.00     ( ( l1_pre_topc @ A ) =>
% 1.81/2.00       ( ![B:$i]:
% 1.81/2.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.81/2.00           ( r1_tarski @
% 1.81/2.00             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 1.81/2.00             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 1.81/2.00  thf('25', plain,
% 1.81/2.00      (![X62 : $i, X63 : $i]:
% 1.81/2.00         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 1.81/2.00          | (r1_tarski @ (k2_tops_1 @ X63 @ (k2_pre_topc @ X63 @ X62)) @ 
% 1.81/2.00             (k2_tops_1 @ X63 @ X62))
% 1.81/2.00          | ~ (l1_pre_topc @ X63))),
% 1.81/2.00      inference('cnf', [status(esa)], [t72_tops_1])).
% 1.81/2.00  thf('26', plain,
% 1.81/2.00      ((~ (l1_pre_topc @ sk_A)
% 1.81/2.00        | (r1_tarski @ 
% 1.81/2.00           (k2_tops_1 @ sk_A @ 
% 1.81/2.00            (k2_pre_topc @ sk_A @ 
% 1.81/2.00             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))) @ 
% 1.81/2.00           (k2_tops_1 @ sk_A @ 
% 1.81/2.00            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.81/2.00      inference('sup-', [status(thm)], ['24', '25'])).
% 1.81/2.00  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf('28', plain,
% 1.81/2.00      ((r1_tarski @ 
% 1.81/2.00        (k2_tops_1 @ sk_A @ 
% 1.81/2.00         (k2_pre_topc @ sk_A @ 
% 1.81/2.00          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))) @ 
% 1.81/2.00        (k2_tops_1 @ sk_A @ 
% 1.81/2.00         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.81/2.00      inference('demod', [status(thm)], ['26', '27'])).
% 1.81/2.00  thf(dt_k2_subset_1, axiom,
% 1.81/2.00    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.81/2.00  thf('29', plain,
% 1.81/2.00      (![X28 : $i]: (m1_subset_1 @ (k2_subset_1 @ X28) @ (k1_zfmisc_1 @ X28))),
% 1.81/2.00      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.81/2.00  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.81/2.00  thf('30', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 1.81/2.00      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.81/2.00  thf('31', plain, (![X28 : $i]: (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X28))),
% 1.81/2.00      inference('demod', [status(thm)], ['29', '30'])).
% 1.81/2.00  thf(t3_subset, axiom,
% 1.81/2.00    (![A:$i,B:$i]:
% 1.81/2.00     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.81/2.00  thf('32', plain,
% 1.81/2.00      (![X44 : $i, X45 : $i]:
% 1.81/2.00         ((r1_tarski @ X44 @ X45) | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 1.81/2.00      inference('cnf', [status(esa)], [t3_subset])).
% 1.81/2.00  thf('33', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.81/2.00      inference('sup-', [status(thm)], ['31', '32'])).
% 1.81/2.00  thf(t11_xboole_1, axiom,
% 1.81/2.00    (![A:$i,B:$i,C:$i]:
% 1.81/2.00     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.81/2.00  thf('34', plain,
% 1.81/2.00      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.81/2.00         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 1.81/2.00      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.81/2.00  thf('35', plain,
% 1.81/2.00      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.81/2.00      inference('sup-', [status(thm)], ['33', '34'])).
% 1.81/2.00  thf('36', plain,
% 1.81/2.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf('37', plain,
% 1.81/2.00      (![X44 : $i, X45 : $i]:
% 1.81/2.00         ((r1_tarski @ X44 @ X45) | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 1.81/2.00      inference('cnf', [status(esa)], [t3_subset])).
% 1.81/2.00  thf('38', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.81/2.00      inference('sup-', [status(thm)], ['36', '37'])).
% 1.81/2.00  thf(t1_xboole_1, axiom,
% 1.81/2.00    (![A:$i,B:$i,C:$i]:
% 1.81/2.00     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.81/2.00       ( r1_tarski @ A @ C ) ))).
% 1.81/2.00  thf('39', plain,
% 1.81/2.00      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.81/2.00         (~ (r1_tarski @ X9 @ X10)
% 1.81/2.00          | ~ (r1_tarski @ X10 @ X11)
% 1.81/2.00          | (r1_tarski @ X9 @ X11))),
% 1.81/2.00      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.81/2.00  thf('40', plain,
% 1.81/2.00      (![X0 : $i]:
% 1.81/2.00         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 1.81/2.00      inference('sup-', [status(thm)], ['38', '39'])).
% 1.81/2.00  thf('41', plain,
% 1.81/2.00      (![X0 : $i]:
% 1.81/2.00         (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 1.81/2.00      inference('sup-', [status(thm)], ['35', '40'])).
% 1.81/2.00  thf(t43_xboole_1, axiom,
% 1.81/2.00    (![A:$i,B:$i,C:$i]:
% 1.81/2.00     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.81/2.00       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.81/2.00  thf('42', plain,
% 1.81/2.00      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.81/2.00         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 1.81/2.00          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 1.81/2.00      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.81/2.00  thf('43', plain,
% 1.81/2.00      (![X0 : $i]:
% 1.81/2.00         (r1_tarski @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 1.81/2.00      inference('sup-', [status(thm)], ['41', '42'])).
% 1.81/2.00  thf(t38_xboole_1, axiom,
% 1.81/2.00    (![A:$i,B:$i]:
% 1.81/2.00     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 1.81/2.00       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.81/2.00  thf('44', plain,
% 1.81/2.00      (![X14 : $i, X15 : $i]:
% 1.81/2.00         (((X14) = (k1_xboole_0))
% 1.81/2.00          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 1.81/2.00      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.81/2.00  thf('45', plain,
% 1.81/2.00      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 1.81/2.00      inference('sup-', [status(thm)], ['43', '44'])).
% 1.81/2.00  thf(t48_xboole_1, axiom,
% 1.81/2.00    (![A:$i,B:$i]:
% 1.81/2.00     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.81/2.00  thf('46', plain,
% 1.81/2.00      (![X20 : $i, X21 : $i]:
% 1.81/2.00         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.81/2.00           = (k3_xboole_0 @ X20 @ X21))),
% 1.81/2.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.81/2.00  thf('47', plain,
% 1.81/2.00      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 1.81/2.00         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('sup+', [status(thm)], ['45', '46'])).
% 1.81/2.00  thf(t4_subset_1, axiom,
% 1.81/2.00    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.81/2.00  thf('48', plain,
% 1.81/2.00      (![X41 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X41))),
% 1.81/2.00      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.81/2.00  thf('49', plain,
% 1.81/2.00      (![X26 : $i, X27 : $i]:
% 1.81/2.00         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 1.81/2.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.81/2.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.81/2.00  thf('50', plain,
% 1.81/2.00      (![X0 : $i]:
% 1.81/2.00         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.81/2.00      inference('sup-', [status(thm)], ['48', '49'])).
% 1.81/2.00  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 1.81/2.00  thf('51', plain, (![X24 : $i]: ((k1_subset_1 @ X24) = (k1_xboole_0))),
% 1.81/2.00      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.81/2.00  thf(t22_subset_1, axiom,
% 1.81/2.00    (![A:$i]:
% 1.81/2.00     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 1.81/2.00  thf('52', plain,
% 1.81/2.00      (![X37 : $i]:
% 1.81/2.00         ((k2_subset_1 @ X37) = (k3_subset_1 @ X37 @ (k1_subset_1 @ X37)))),
% 1.81/2.00      inference('cnf', [status(esa)], [t22_subset_1])).
% 1.81/2.00  thf('53', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 1.81/2.00      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.81/2.00  thf('54', plain,
% 1.81/2.00      (![X37 : $i]: ((X37) = (k3_subset_1 @ X37 @ (k1_subset_1 @ X37)))),
% 1.81/2.00      inference('demod', [status(thm)], ['52', '53'])).
% 1.81/2.00  thf('55', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.81/2.00      inference('sup+', [status(thm)], ['51', '54'])).
% 1.81/2.00  thf('56', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.81/2.00      inference('sup+', [status(thm)], ['50', '55'])).
% 1.81/2.00  thf('57', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('demod', [status(thm)], ['47', '56'])).
% 1.81/2.00  thf(commutativity_k2_tarski, axiom,
% 1.81/2.00    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.81/2.00  thf('58', plain,
% 1.81/2.00      (![X22 : $i, X23 : $i]:
% 1.81/2.00         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 1.81/2.00      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.81/2.00  thf(t12_setfam_1, axiom,
% 1.81/2.00    (![A:$i,B:$i]:
% 1.81/2.00     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.81/2.00  thf('59', plain,
% 1.81/2.00      (![X42 : $i, X43 : $i]:
% 1.81/2.00         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 1.81/2.00      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.81/2.00  thf('60', plain,
% 1.81/2.00      (![X0 : $i, X1 : $i]:
% 1.81/2.00         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.81/2.00      inference('sup+', [status(thm)], ['58', '59'])).
% 1.81/2.00  thf('61', plain,
% 1.81/2.00      (![X42 : $i, X43 : $i]:
% 1.81/2.00         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 1.81/2.00      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.81/2.00  thf('62', plain,
% 1.81/2.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.81/2.00      inference('sup+', [status(thm)], ['60', '61'])).
% 1.81/2.00  thf(t100_xboole_1, axiom,
% 1.81/2.00    (![A:$i,B:$i]:
% 1.81/2.00     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.81/2.00  thf('63', plain,
% 1.81/2.00      (![X2 : $i, X3 : $i]:
% 1.81/2.00         ((k4_xboole_0 @ X2 @ X3)
% 1.81/2.00           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 1.81/2.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.81/2.00  thf('64', plain,
% 1.81/2.00      (![X0 : $i, X1 : $i]:
% 1.81/2.00         ((k4_xboole_0 @ X0 @ X1)
% 1.81/2.00           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.81/2.00      inference('sup+', [status(thm)], ['62', '63'])).
% 1.81/2.00  thf('65', plain,
% 1.81/2.00      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.81/2.00         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.81/2.00      inference('sup+', [status(thm)], ['57', '64'])).
% 1.81/2.00  thf('66', plain,
% 1.81/2.00      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.81/2.00         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.81/2.00      inference('sup+', [status(thm)], ['57', '64'])).
% 1.81/2.00  thf(t36_xboole_1, axiom,
% 1.81/2.00    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.81/2.00  thf('67', plain,
% 1.81/2.00      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.81/2.00      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.81/2.00  thf('68', plain,
% 1.81/2.00      (![X44 : $i, X46 : $i]:
% 1.81/2.00         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 1.81/2.00      inference('cnf', [status(esa)], [t3_subset])).
% 1.81/2.00  thf('69', plain,
% 1.81/2.00      (![X0 : $i, X1 : $i]:
% 1.81/2.00         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.81/2.00      inference('sup-', [status(thm)], ['67', '68'])).
% 1.81/2.00  thf('70', plain,
% 1.81/2.00      (![X26 : $i, X27 : $i]:
% 1.81/2.00         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 1.81/2.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.81/2.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.81/2.00  thf('71', plain,
% 1.81/2.00      (![X0 : $i, X1 : $i]:
% 1.81/2.00         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.81/2.00           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.81/2.00      inference('sup-', [status(thm)], ['69', '70'])).
% 1.81/2.00  thf('72', plain,
% 1.81/2.00      (![X20 : $i, X21 : $i]:
% 1.81/2.00         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.81/2.00           = (k3_xboole_0 @ X20 @ X21))),
% 1.81/2.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.81/2.00  thf('73', plain,
% 1.81/2.00      (![X0 : $i, X1 : $i]:
% 1.81/2.00         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.81/2.00           = (k3_xboole_0 @ X0 @ X1))),
% 1.81/2.00      inference('demod', [status(thm)], ['71', '72'])).
% 1.81/2.00  thf('74', plain,
% 1.81/2.00      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.81/2.00         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.81/2.00      inference('sup+', [status(thm)], ['66', '73'])).
% 1.81/2.00  thf('75', plain,
% 1.81/2.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.81/2.00      inference('sup+', [status(thm)], ['60', '61'])).
% 1.81/2.00  thf('76', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('demod', [status(thm)], ['47', '56'])).
% 1.81/2.00  thf('77', plain,
% 1.81/2.00      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.81/2.00      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.81/2.00  thf('78', plain,
% 1.81/2.00      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.81/2.00         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.81/2.00      inference('sup+', [status(thm)], ['57', '64'])).
% 1.81/2.00  thf('79', plain,
% 1.81/2.00      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.81/2.00      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.81/2.00  thf('80', plain,
% 1.81/2.00      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.81/2.00        (k2_tops_1 @ sk_A @ sk_B))),
% 1.81/2.00      inference('demod', [status(thm)], ['28', '65', '77', '78', '79'])).
% 1.81/2.00  thf('81', plain,
% 1.81/2.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf(dt_k2_pre_topc, axiom,
% 1.81/2.00    (![A:$i,B:$i]:
% 1.81/2.00     ( ( ( l1_pre_topc @ A ) & 
% 1.81/2.00         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.81/2.00       ( m1_subset_1 @
% 1.81/2.00         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.81/2.00  thf('82', plain,
% 1.81/2.00      (![X50 : $i, X51 : $i]:
% 1.81/2.00         (~ (l1_pre_topc @ X50)
% 1.81/2.00          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 1.81/2.00          | (m1_subset_1 @ (k2_pre_topc @ X50 @ X51) @ 
% 1.81/2.00             (k1_zfmisc_1 @ (u1_struct_0 @ X50))))),
% 1.81/2.00      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.81/2.00  thf('83', plain,
% 1.81/2.00      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.81/2.00         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.81/2.00        | ~ (l1_pre_topc @ sk_A))),
% 1.81/2.00      inference('sup-', [status(thm)], ['81', '82'])).
% 1.81/2.00  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf('85', plain,
% 1.81/2.00      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.81/2.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('demod', [status(thm)], ['83', '84'])).
% 1.81/2.00  thf('86', plain,
% 1.81/2.00      (![X29 : $i, X30 : $i]:
% 1.81/2.00         ((m1_subset_1 @ (k3_subset_1 @ X29 @ X30) @ (k1_zfmisc_1 @ X29))
% 1.81/2.00          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 1.81/2.00      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.81/2.00  thf('87', plain,
% 1.81/2.00      ((m1_subset_1 @ 
% 1.81/2.00        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.81/2.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('sup-', [status(thm)], ['85', '86'])).
% 1.81/2.00  thf('88', plain,
% 1.81/2.00      (![X29 : $i, X30 : $i]:
% 1.81/2.00         ((m1_subset_1 @ (k3_subset_1 @ X29 @ X30) @ (k1_zfmisc_1 @ X29))
% 1.81/2.00          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 1.81/2.00      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.81/2.00  thf('89', plain,
% 1.81/2.00      ((m1_subset_1 @ 
% 1.81/2.00        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 1.81/2.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('sup-', [status(thm)], ['87', '88'])).
% 1.81/2.00  thf('90', plain,
% 1.81/2.00      (![X64 : $i, X65 : $i]:
% 1.81/2.00         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 1.81/2.00          | ~ (v2_tops_1 @ X64 @ X65)
% 1.81/2.00          | (r1_tarski @ X64 @ (k2_tops_1 @ X65 @ X64))
% 1.81/2.00          | ~ (l1_pre_topc @ X65))),
% 1.81/2.00      inference('cnf', [status(esa)], [t88_tops_1])).
% 1.81/2.00  thf('91', plain,
% 1.81/2.00      ((~ (l1_pre_topc @ sk_A)
% 1.81/2.00        | (r1_tarski @ 
% 1.81/2.00           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 1.81/2.00           (k2_tops_1 @ sk_A @ 
% 1.81/2.00            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))))
% 1.81/2.00        | ~ (v2_tops_1 @ 
% 1.81/2.00             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 1.81/2.00             sk_A))),
% 1.81/2.00      inference('sup-', [status(thm)], ['89', '90'])).
% 1.81/2.00  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf('93', plain,
% 1.81/2.00      (((r1_tarski @ 
% 1.81/2.00         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 1.81/2.00         (k2_tops_1 @ sk_A @ 
% 1.81/2.00          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))))
% 1.81/2.00        | ~ (v2_tops_1 @ 
% 1.81/2.00             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.81/2.00              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 1.81/2.00             sk_A))),
% 1.81/2.00      inference('demod', [status(thm)], ['91', '92'])).
% 1.81/2.00  thf('94', plain,
% 1.81/2.00      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.81/2.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('demod', [status(thm)], ['83', '84'])).
% 1.81/2.00  thf('95', plain,
% 1.81/2.00      (![X26 : $i, X27 : $i]:
% 1.81/2.00         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 1.81/2.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.81/2.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.81/2.00  thf('96', plain,
% 1.81/2.00      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 1.81/2.00         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.81/2.00      inference('sup-', [status(thm)], ['94', '95'])).
% 1.81/2.00  thf('97', plain,
% 1.81/2.00      (![X0 : $i, X1 : $i]:
% 1.81/2.00         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.81/2.00           = (k3_xboole_0 @ X0 @ X1))),
% 1.81/2.00      inference('demod', [status(thm)], ['71', '72'])).
% 1.81/2.00  thf('98', plain,
% 1.81/2.00      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.81/2.00      inference('sup-', [status(thm)], ['33', '34'])).
% 1.81/2.00  thf('99', plain,
% 1.81/2.00      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.81/2.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('demod', [status(thm)], ['83', '84'])).
% 1.81/2.00  thf('100', plain,
% 1.81/2.00      (![X44 : $i, X45 : $i]:
% 1.81/2.00         ((r1_tarski @ X44 @ X45) | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 1.81/2.00      inference('cnf', [status(esa)], [t3_subset])).
% 1.81/2.00  thf('101', plain,
% 1.81/2.00      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.81/2.00      inference('sup-', [status(thm)], ['99', '100'])).
% 1.81/2.00  thf('102', plain,
% 1.81/2.00      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.81/2.00         (~ (r1_tarski @ X9 @ X10)
% 1.81/2.00          | ~ (r1_tarski @ X10 @ X11)
% 1.81/2.00          | (r1_tarski @ X9 @ X11))),
% 1.81/2.00      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.81/2.00  thf('103', plain,
% 1.81/2.00      (![X0 : $i]:
% 1.81/2.00         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 1.81/2.00          | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 1.81/2.00      inference('sup-', [status(thm)], ['101', '102'])).
% 1.81/2.00  thf('104', plain,
% 1.81/2.00      (![X0 : $i]:
% 1.81/2.00         (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.81/2.00          (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 1.81/2.00      inference('sup-', [status(thm)], ['98', '103'])).
% 1.81/2.00  thf('105', plain,
% 1.81/2.00      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.81/2.00         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 1.81/2.00          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 1.81/2.00      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.81/2.00  thf('106', plain,
% 1.81/2.00      (![X0 : $i]:
% 1.81/2.00         (r1_tarski @ 
% 1.81/2.00          (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 1.81/2.00          X0)),
% 1.81/2.00      inference('sup-', [status(thm)], ['104', '105'])).
% 1.81/2.00  thf('107', plain,
% 1.81/2.00      (![X14 : $i, X15 : $i]:
% 1.81/2.00         (((X14) = (k1_xboole_0))
% 1.81/2.00          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 1.81/2.00      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.81/2.00  thf('108', plain,
% 1.81/2.00      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.81/2.00         = (k1_xboole_0))),
% 1.81/2.00      inference('sup-', [status(thm)], ['106', '107'])).
% 1.81/2.00  thf('109', plain,
% 1.81/2.00      (![X20 : $i, X21 : $i]:
% 1.81/2.00         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.81/2.00           = (k3_xboole_0 @ X20 @ X21))),
% 1.81/2.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.81/2.00  thf('110', plain,
% 1.81/2.00      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ k1_xboole_0)
% 1.81/2.00         = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('sup+', [status(thm)], ['108', '109'])).
% 1.81/2.00  thf('111', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.81/2.00      inference('sup+', [status(thm)], ['50', '55'])).
% 1.81/2.00  thf('112', plain,
% 1.81/2.00      (((k2_pre_topc @ sk_A @ sk_B)
% 1.81/2.00         = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('demod', [status(thm)], ['110', '111'])).
% 1.81/2.00  thf('113', plain,
% 1.81/2.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.81/2.00      inference('sup+', [status(thm)], ['60', '61'])).
% 1.81/2.00  thf('114', plain,
% 1.81/2.00      (((k2_pre_topc @ sk_A @ sk_B)
% 1.81/2.00         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.81/2.00      inference('demod', [status(thm)], ['112', '113'])).
% 1.81/2.00  thf('115', plain,
% 1.81/2.00      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 1.81/2.00         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.81/2.00      inference('sup-', [status(thm)], ['94', '95'])).
% 1.81/2.00  thf('116', plain,
% 1.81/2.00      (![X0 : $i, X1 : $i]:
% 1.81/2.00         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.81/2.00           = (k3_xboole_0 @ X0 @ X1))),
% 1.81/2.00      inference('demod', [status(thm)], ['71', '72'])).
% 1.81/2.00  thf('117', plain,
% 1.81/2.00      (((k2_pre_topc @ sk_A @ sk_B)
% 1.81/2.00         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.81/2.00      inference('demod', [status(thm)], ['112', '113'])).
% 1.81/2.00  thf('118', plain,
% 1.81/2.00      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 1.81/2.00         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.81/2.00      inference('sup-', [status(thm)], ['94', '95'])).
% 1.81/2.00  thf('119', plain,
% 1.81/2.00      (![X0 : $i, X1 : $i]:
% 1.81/2.00         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.81/2.00           = (k3_xboole_0 @ X0 @ X1))),
% 1.81/2.00      inference('demod', [status(thm)], ['71', '72'])).
% 1.81/2.00  thf('120', plain,
% 1.81/2.00      (((k2_pre_topc @ sk_A @ sk_B)
% 1.81/2.00         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.81/2.00      inference('demod', [status(thm)], ['112', '113'])).
% 1.81/2.00  thf('121', plain,
% 1.81/2.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf(d5_tops_1, axiom,
% 1.81/2.00    (![A:$i]:
% 1.81/2.00     ( ( l1_pre_topc @ A ) =>
% 1.81/2.00       ( ![B:$i]:
% 1.81/2.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.81/2.00           ( ( v3_tops_1 @ B @ A ) <=>
% 1.81/2.00             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 1.81/2.00  thf('122', plain,
% 1.81/2.00      (![X54 : $i, X55 : $i]:
% 1.81/2.00         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 1.81/2.00          | ~ (v3_tops_1 @ X54 @ X55)
% 1.81/2.00          | (v2_tops_1 @ (k2_pre_topc @ X55 @ X54) @ X55)
% 1.81/2.00          | ~ (l1_pre_topc @ X55))),
% 1.81/2.00      inference('cnf', [status(esa)], [d5_tops_1])).
% 1.81/2.00  thf('123', plain,
% 1.81/2.00      ((~ (l1_pre_topc @ sk_A)
% 1.81/2.00        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.81/2.00        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 1.81/2.00      inference('sup-', [status(thm)], ['121', '122'])).
% 1.81/2.00  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf('125', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf('126', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.81/2.00      inference('demod', [status(thm)], ['123', '124', '125'])).
% 1.81/2.00  thf('127', plain,
% 1.81/2.00      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.81/2.00        (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.81/2.00      inference('demod', [status(thm)],
% 1.81/2.00                ['93', '96', '97', '114', '115', '116', '117', '118', '119', 
% 1.81/2.00                 '120', '126'])).
% 1.81/2.00  thf('128', plain,
% 1.81/2.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf(t65_tops_1, axiom,
% 1.81/2.00    (![A:$i]:
% 1.81/2.00     ( ( l1_pre_topc @ A ) =>
% 1.81/2.00       ( ![B:$i]:
% 1.81/2.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.81/2.00           ( ( k2_pre_topc @ A @ B ) =
% 1.81/2.00             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.81/2.00  thf('129', plain,
% 1.81/2.00      (![X60 : $i, X61 : $i]:
% 1.81/2.00         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 1.81/2.00          | ((k2_pre_topc @ X61 @ X60)
% 1.81/2.00              = (k4_subset_1 @ (u1_struct_0 @ X61) @ X60 @ 
% 1.81/2.00                 (k2_tops_1 @ X61 @ X60)))
% 1.81/2.00          | ~ (l1_pre_topc @ X61))),
% 1.81/2.00      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.81/2.00  thf('130', plain,
% 1.81/2.00      ((~ (l1_pre_topc @ sk_A)
% 1.81/2.00        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.81/2.00            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.81/2.00               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.81/2.00      inference('sup-', [status(thm)], ['128', '129'])).
% 1.81/2.00  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf('132', plain,
% 1.81/2.00      (((k2_pre_topc @ sk_A @ sk_B)
% 1.81/2.00         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.81/2.00            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.81/2.00      inference('demod', [status(thm)], ['130', '131'])).
% 1.81/2.00  thf('133', plain,
% 1.81/2.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf(dt_k2_tops_1, axiom,
% 1.81/2.00    (![A:$i,B:$i]:
% 1.81/2.00     ( ( ( l1_pre_topc @ A ) & 
% 1.81/2.00         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.81/2.00       ( m1_subset_1 @
% 1.81/2.00         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.81/2.00  thf('134', plain,
% 1.81/2.00      (![X56 : $i, X57 : $i]:
% 1.81/2.00         (~ (l1_pre_topc @ X56)
% 1.81/2.00          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 1.81/2.00          | (m1_subset_1 @ (k2_tops_1 @ X56 @ X57) @ 
% 1.81/2.00             (k1_zfmisc_1 @ (u1_struct_0 @ X56))))),
% 1.81/2.00      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.81/2.00  thf('135', plain,
% 1.81/2.00      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.81/2.00         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.81/2.00        | ~ (l1_pre_topc @ sk_A))),
% 1.81/2.00      inference('sup-', [status(thm)], ['133', '134'])).
% 1.81/2.00  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf('137', plain,
% 1.81/2.00      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.81/2.00        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('demod', [status(thm)], ['135', '136'])).
% 1.81/2.00  thf('138', plain,
% 1.81/2.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.81/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.00  thf(redefinition_k4_subset_1, axiom,
% 1.81/2.00    (![A:$i,B:$i,C:$i]:
% 1.81/2.00     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.81/2.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.81/2.00       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.81/2.00  thf('139', plain,
% 1.81/2.00      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.81/2.00         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 1.81/2.00          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 1.81/2.00          | ((k4_subset_1 @ X32 @ X31 @ X33) = (k2_xboole_0 @ X31 @ X33)))),
% 1.81/2.00      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.81/2.00  thf('140', plain,
% 1.81/2.00      (![X0 : $i]:
% 1.81/2.00         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.81/2.00            = (k2_xboole_0 @ sk_B @ X0))
% 1.81/2.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.81/2.00      inference('sup-', [status(thm)], ['138', '139'])).
% 1.81/2.00  thf('141', plain,
% 1.81/2.00      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.81/2.00         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.81/2.01      inference('sup-', [status(thm)], ['137', '140'])).
% 1.81/2.01  thf('142', plain,
% 1.81/2.01      (((k2_pre_topc @ sk_A @ sk_B)
% 1.81/2.01         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.81/2.01      inference('sup+', [status(thm)], ['132', '141'])).
% 1.81/2.01  thf('143', plain,
% 1.81/2.01      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.81/2.01         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 1.81/2.01      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.81/2.01  thf('144', plain,
% 1.81/2.01      (![X0 : $i]:
% 1.81/2.01         (~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 1.81/2.01          | (r1_tarski @ sk_B @ X0))),
% 1.81/2.01      inference('sup-', [status(thm)], ['142', '143'])).
% 1.81/2.01  thf('145', plain,
% 1.81/2.01      ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.81/2.01      inference('sup-', [status(thm)], ['127', '144'])).
% 1.81/2.01  thf('146', plain,
% 1.81/2.01      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.81/2.01         (~ (r1_tarski @ X9 @ X10)
% 1.81/2.01          | ~ (r1_tarski @ X10 @ X11)
% 1.81/2.01          | (r1_tarski @ X9 @ X11))),
% 1.81/2.01      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.81/2.01  thf('147', plain,
% 1.81/2.01      (![X0 : $i]:
% 1.81/2.01         ((r1_tarski @ sk_B @ X0)
% 1.81/2.01          | ~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.81/2.01               X0))),
% 1.81/2.01      inference('sup-', [status(thm)], ['145', '146'])).
% 1.81/2.01  thf('148', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 1.81/2.01      inference('sup-', [status(thm)], ['80', '147'])).
% 1.81/2.01  thf('149', plain, ($false), inference('demod', [status(thm)], ['17', '148'])).
% 1.81/2.01  
% 1.81/2.01  % SZS output end Refutation
% 1.81/2.01  
% 1.81/2.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
