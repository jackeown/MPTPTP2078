%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YfSiDjw2Sy

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:59 EST 2020

% Result     : Theorem 6.05s
% Output     : Refutation 6.05s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 312 expanded)
%              Number of leaves         :   36 ( 102 expanded)
%              Depth                    :   17
%              Number of atoms          : 1399 (3849 expanded)
%              Number of equality atoms :   35 ( 139 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) ) ) ),
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

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('5',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X38 @ X37 ) @ X37 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k2_pre_topc @ X46 @ X45 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X46 ) @ X45 @ ( k2_tops_1 @ X46 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k4_subset_1 @ X18 @ X17 @ X19 )
        = ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( r1_tarski @ X39 @ X41 )
      | ( r1_tarski @ ( k1_tops_1 @ X40 @ X39 ) @ ( k1_tops_1 @ X40 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k1_tops_1 @ X35 @ ( k1_tops_1 @ X35 @ X36 ) )
        = ( k1_tops_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('43',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('47',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','45','46','47'])).

thf('49',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('51',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( r1_tarski @ X39 @ X41 )
      | ( r1_tarski @ ( k1_tops_1 @ X40 @ X39 ) @ ( k1_tops_1 @ X40 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('62',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r1_tarski @ X25 @ ( k2_pre_topc @ X26 @ X25 ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
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

thf('70',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v4_tops_1 @ X27 @ X28 )
      | ( r1_tarski @ ( k1_tops_1 @ X28 @ ( k2_pre_topc @ X28 @ X27 ) ) @ X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('76',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('77',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( r1_tarski @ X39 @ X41 )
      | ( r1_tarski @ ( k1_tops_1 @ X40 @ X39 ) @ ( k1_tops_1 @ X40 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('84',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k1_tops_1 @ X35 @ ( k1_tops_1 @ X35 @ X36 ) )
        = ( k1_tops_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('85',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','87'])).

thf('89',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['68','91'])).

thf('93',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('94',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','92','93'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('95',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
      | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('101',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( ( k1_tops_1 @ X48 @ X47 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X48 ) @ X47 @ ( k2_tops_1 @ X48 @ X47 ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('102',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('105',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','103','106'])).

thf('108',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('109',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['107','110'])).

thf('112',plain,(
    $false ),
    inference(demod,[status(thm)],['99','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YfSiDjw2Sy
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:53:52 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.36  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 6.05/6.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.05/6.28  % Solved by: fo/fo7.sh
% 6.05/6.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.05/6.28  % done 4504 iterations in 5.771s
% 6.05/6.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.05/6.28  % SZS output start Refutation
% 6.05/6.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.05/6.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.05/6.28  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 6.05/6.28  thf(sk_B_type, type, sk_B: $i).
% 6.05/6.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.05/6.28  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 6.05/6.28  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.05/6.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.05/6.28  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 6.05/6.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.05/6.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.05/6.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.05/6.28  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.05/6.28  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 6.05/6.28  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 6.05/6.28  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 6.05/6.28  thf(sk_A_type, type, sk_A: $i).
% 6.05/6.28  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.05/6.28  thf(t110_tops_1, conjecture,
% 6.05/6.28    (![A:$i]:
% 6.05/6.28     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.05/6.28       ( ![B:$i]:
% 6.05/6.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.05/6.28           ( ( v4_tops_1 @ B @ A ) =>
% 6.05/6.28             ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 6.05/6.28  thf(zf_stmt_0, negated_conjecture,
% 6.05/6.28    (~( ![A:$i]:
% 6.05/6.28        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.05/6.28          ( ![B:$i]:
% 6.05/6.28            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.05/6.28              ( ( v4_tops_1 @ B @ A ) =>
% 6.05/6.28                ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 6.05/6.28    inference('cnf.neg', [status(esa)], [t110_tops_1])).
% 6.05/6.28  thf('0', plain,
% 6.05/6.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf(dt_k2_tops_1, axiom,
% 6.05/6.28    (![A:$i,B:$i]:
% 6.05/6.28     ( ( ( l1_pre_topc @ A ) & 
% 6.05/6.28         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.05/6.28       ( m1_subset_1 @
% 6.05/6.28         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 6.05/6.28  thf('1', plain,
% 6.05/6.28      (![X31 : $i, X32 : $i]:
% 6.05/6.28         (~ (l1_pre_topc @ X31)
% 6.05/6.28          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 6.05/6.28          | (m1_subset_1 @ (k2_tops_1 @ X31 @ X32) @ 
% 6.05/6.28             (k1_zfmisc_1 @ (u1_struct_0 @ X31))))),
% 6.05/6.28      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 6.05/6.28  thf('2', plain,
% 6.05/6.28      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.28         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.28        | ~ (l1_pre_topc @ sk_A))),
% 6.05/6.28      inference('sup-', [status(thm)], ['0', '1'])).
% 6.05/6.28  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('4', plain,
% 6.05/6.28      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('demod', [status(thm)], ['2', '3'])).
% 6.05/6.28  thf(t44_tops_1, axiom,
% 6.05/6.28    (![A:$i]:
% 6.05/6.28     ( ( l1_pre_topc @ A ) =>
% 6.05/6.28       ( ![B:$i]:
% 6.05/6.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.05/6.28           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 6.05/6.28  thf('5', plain,
% 6.05/6.28      (![X37 : $i, X38 : $i]:
% 6.05/6.28         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 6.05/6.28          | (r1_tarski @ (k1_tops_1 @ X38 @ X37) @ X37)
% 6.05/6.28          | ~ (l1_pre_topc @ X38))),
% 6.05/6.28      inference('cnf', [status(esa)], [t44_tops_1])).
% 6.05/6.28  thf('6', plain,
% 6.05/6.28      ((~ (l1_pre_topc @ sk_A)
% 6.05/6.28        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 6.05/6.28           (k2_tops_1 @ sk_A @ sk_B)))),
% 6.05/6.28      inference('sup-', [status(thm)], ['4', '5'])).
% 6.05/6.28  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('8', plain,
% 6.05/6.28      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 6.05/6.28        (k2_tops_1 @ sk_A @ sk_B))),
% 6.05/6.28      inference('demod', [status(thm)], ['6', '7'])).
% 6.05/6.28  thf('9', plain,
% 6.05/6.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf(t65_tops_1, axiom,
% 6.05/6.28    (![A:$i]:
% 6.05/6.28     ( ( l1_pre_topc @ A ) =>
% 6.05/6.28       ( ![B:$i]:
% 6.05/6.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.05/6.28           ( ( k2_pre_topc @ A @ B ) =
% 6.05/6.28             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 6.05/6.28  thf('10', plain,
% 6.05/6.28      (![X45 : $i, X46 : $i]:
% 6.05/6.28         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 6.05/6.28          | ((k2_pre_topc @ X46 @ X45)
% 6.05/6.28              = (k4_subset_1 @ (u1_struct_0 @ X46) @ X45 @ 
% 6.05/6.28                 (k2_tops_1 @ X46 @ X45)))
% 6.05/6.28          | ~ (l1_pre_topc @ X46))),
% 6.05/6.28      inference('cnf', [status(esa)], [t65_tops_1])).
% 6.05/6.28  thf('11', plain,
% 6.05/6.28      ((~ (l1_pre_topc @ sk_A)
% 6.05/6.28        | ((k2_pre_topc @ sk_A @ sk_B)
% 6.05/6.28            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 6.05/6.28               (k2_tops_1 @ sk_A @ sk_B))))),
% 6.05/6.28      inference('sup-', [status(thm)], ['9', '10'])).
% 6.05/6.28  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('13', plain,
% 6.05/6.28      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('demod', [status(thm)], ['2', '3'])).
% 6.05/6.28  thf('14', plain,
% 6.05/6.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf(redefinition_k4_subset_1, axiom,
% 6.05/6.28    (![A:$i,B:$i,C:$i]:
% 6.05/6.28     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 6.05/6.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 6.05/6.28       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 6.05/6.28  thf('15', plain,
% 6.05/6.28      (![X17 : $i, X18 : $i, X19 : $i]:
% 6.05/6.28         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 6.05/6.28          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 6.05/6.28          | ((k4_subset_1 @ X18 @ X17 @ X19) = (k2_xboole_0 @ X17 @ X19)))),
% 6.05/6.28      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 6.05/6.28  thf('16', plain,
% 6.05/6.28      (![X0 : $i]:
% 6.05/6.28         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 6.05/6.28            = (k2_xboole_0 @ sk_B @ X0))
% 6.05/6.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.05/6.28      inference('sup-', [status(thm)], ['14', '15'])).
% 6.05/6.28  thf('17', plain,
% 6.05/6.28      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 6.05/6.28         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 6.05/6.28      inference('sup-', [status(thm)], ['13', '16'])).
% 6.05/6.28  thf('18', plain,
% 6.05/6.28      (((k2_pre_topc @ sk_A @ sk_B)
% 6.05/6.28         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 6.05/6.28      inference('demod', [status(thm)], ['11', '12', '17'])).
% 6.05/6.28  thf(d10_xboole_0, axiom,
% 6.05/6.28    (![A:$i,B:$i]:
% 6.05/6.28     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.05/6.28  thf('19', plain,
% 6.05/6.28      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 6.05/6.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.05/6.28  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.05/6.28      inference('simplify', [status(thm)], ['19'])).
% 6.05/6.28  thf(t10_xboole_1, axiom,
% 6.05/6.28    (![A:$i,B:$i,C:$i]:
% 6.05/6.28     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 6.05/6.28  thf('21', plain,
% 6.05/6.28      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.05/6.28         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ X8 @ (k2_xboole_0 @ X10 @ X9)))),
% 6.05/6.28      inference('cnf', [status(esa)], [t10_xboole_1])).
% 6.05/6.28  thf('22', plain,
% 6.05/6.28      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 6.05/6.28      inference('sup-', [status(thm)], ['20', '21'])).
% 6.05/6.28  thf('23', plain,
% 6.05/6.28      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))),
% 6.05/6.28      inference('sup+', [status(thm)], ['18', '22'])).
% 6.05/6.28  thf('24', plain,
% 6.05/6.28      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 6.05/6.28        (k2_tops_1 @ sk_A @ sk_B))),
% 6.05/6.28      inference('demod', [status(thm)], ['6', '7'])).
% 6.05/6.28  thf(t1_xboole_1, axiom,
% 6.05/6.28    (![A:$i,B:$i,C:$i]:
% 6.05/6.28     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 6.05/6.28       ( r1_tarski @ A @ C ) ))).
% 6.05/6.28  thf('25', plain,
% 6.05/6.28      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.05/6.28         (~ (r1_tarski @ X11 @ X12)
% 6.05/6.28          | ~ (r1_tarski @ X12 @ X13)
% 6.05/6.28          | (r1_tarski @ X11 @ X13))),
% 6.05/6.28      inference('cnf', [status(esa)], [t1_xboole_1])).
% 6.05/6.28  thf('26', plain,
% 6.05/6.28      (![X0 : $i]:
% 6.05/6.28         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 6.05/6.28          | ~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0))),
% 6.05/6.28      inference('sup-', [status(thm)], ['24', '25'])).
% 6.05/6.28  thf('27', plain,
% 6.05/6.28      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 6.05/6.28        (k2_pre_topc @ sk_A @ sk_B))),
% 6.05/6.28      inference('sup-', [status(thm)], ['23', '26'])).
% 6.05/6.28  thf('28', plain,
% 6.05/6.28      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('demod', [status(thm)], ['2', '3'])).
% 6.05/6.28  thf(dt_k1_tops_1, axiom,
% 6.05/6.28    (![A:$i,B:$i]:
% 6.05/6.28     ( ( ( l1_pre_topc @ A ) & 
% 6.05/6.28         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.05/6.28       ( m1_subset_1 @
% 6.05/6.28         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 6.05/6.28  thf('29', plain,
% 6.05/6.28      (![X29 : $i, X30 : $i]:
% 6.05/6.28         (~ (l1_pre_topc @ X29)
% 6.05/6.28          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 6.05/6.28          | (m1_subset_1 @ (k1_tops_1 @ X29 @ X30) @ 
% 6.05/6.28             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 6.05/6.28      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 6.05/6.28  thf('30', plain,
% 6.05/6.28      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 6.05/6.28         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.28        | ~ (l1_pre_topc @ sk_A))),
% 6.05/6.28      inference('sup-', [status(thm)], ['28', '29'])).
% 6.05/6.28  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('32', plain,
% 6.05/6.28      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 6.05/6.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('demod', [status(thm)], ['30', '31'])).
% 6.05/6.28  thf('33', plain,
% 6.05/6.28      (![X29 : $i, X30 : $i]:
% 6.05/6.28         (~ (l1_pre_topc @ X29)
% 6.05/6.28          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 6.05/6.28          | (m1_subset_1 @ (k1_tops_1 @ X29 @ X30) @ 
% 6.05/6.28             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 6.05/6.28      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 6.05/6.28  thf('34', plain,
% 6.05/6.28      (((m1_subset_1 @ 
% 6.05/6.28         (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 6.05/6.28         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.28        | ~ (l1_pre_topc @ sk_A))),
% 6.05/6.28      inference('sup-', [status(thm)], ['32', '33'])).
% 6.05/6.28  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('36', plain,
% 6.05/6.28      ((m1_subset_1 @ 
% 6.05/6.28        (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 6.05/6.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('demod', [status(thm)], ['34', '35'])).
% 6.05/6.28  thf(t48_tops_1, axiom,
% 6.05/6.28    (![A:$i]:
% 6.05/6.28     ( ( l1_pre_topc @ A ) =>
% 6.05/6.28       ( ![B:$i]:
% 6.05/6.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.05/6.28           ( ![C:$i]:
% 6.05/6.28             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.05/6.28               ( ( r1_tarski @ B @ C ) =>
% 6.05/6.28                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 6.05/6.28  thf('37', plain,
% 6.05/6.28      (![X39 : $i, X40 : $i, X41 : $i]:
% 6.05/6.28         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 6.05/6.28          | ~ (r1_tarski @ X39 @ X41)
% 6.05/6.28          | (r1_tarski @ (k1_tops_1 @ X40 @ X39) @ (k1_tops_1 @ X40 @ X41))
% 6.05/6.28          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 6.05/6.28          | ~ (l1_pre_topc @ X40))),
% 6.05/6.28      inference('cnf', [status(esa)], [t48_tops_1])).
% 6.05/6.28  thf('38', plain,
% 6.05/6.28      (![X0 : $i]:
% 6.05/6.28         (~ (l1_pre_topc @ sk_A)
% 6.05/6.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.28          | (r1_tarski @ 
% 6.05/6.28             (k1_tops_1 @ sk_A @ 
% 6.05/6.28              (k1_tops_1 @ sk_A @ 
% 6.05/6.28               (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))) @ 
% 6.05/6.28             (k1_tops_1 @ sk_A @ X0))
% 6.05/6.28          | ~ (r1_tarski @ 
% 6.05/6.28               (k1_tops_1 @ sk_A @ 
% 6.05/6.28                (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 6.05/6.28               X0))),
% 6.05/6.28      inference('sup-', [status(thm)], ['36', '37'])).
% 6.05/6.28  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('40', plain,
% 6.05/6.28      (![X0 : $i]:
% 6.05/6.28         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.28          | (r1_tarski @ 
% 6.05/6.28             (k1_tops_1 @ sk_A @ 
% 6.05/6.28              (k1_tops_1 @ sk_A @ 
% 6.05/6.28               (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))) @ 
% 6.05/6.28             (k1_tops_1 @ sk_A @ X0))
% 6.05/6.28          | ~ (r1_tarski @ 
% 6.05/6.28               (k1_tops_1 @ sk_A @ 
% 6.05/6.28                (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 6.05/6.28               X0))),
% 6.05/6.28      inference('demod', [status(thm)], ['38', '39'])).
% 6.05/6.28  thf('41', plain,
% 6.05/6.28      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('demod', [status(thm)], ['2', '3'])).
% 6.05/6.28  thf(projectivity_k1_tops_1, axiom,
% 6.05/6.28    (![A:$i,B:$i]:
% 6.05/6.28     ( ( ( l1_pre_topc @ A ) & 
% 6.05/6.28         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.05/6.28       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 6.05/6.28  thf('42', plain,
% 6.05/6.28      (![X35 : $i, X36 : $i]:
% 6.05/6.28         (~ (l1_pre_topc @ X35)
% 6.05/6.28          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 6.05/6.28          | ((k1_tops_1 @ X35 @ (k1_tops_1 @ X35 @ X36))
% 6.05/6.28              = (k1_tops_1 @ X35 @ X36)))),
% 6.05/6.28      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 6.05/6.28  thf('43', plain,
% 6.05/6.28      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 6.05/6.28          = (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 6.05/6.28        | ~ (l1_pre_topc @ sk_A))),
% 6.05/6.28      inference('sup-', [status(thm)], ['41', '42'])).
% 6.05/6.28  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('45', plain,
% 6.05/6.28      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 6.05/6.28         = (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 6.05/6.28      inference('demod', [status(thm)], ['43', '44'])).
% 6.05/6.28  thf('46', plain,
% 6.05/6.28      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 6.05/6.28         = (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 6.05/6.28      inference('demod', [status(thm)], ['43', '44'])).
% 6.05/6.28  thf('47', plain,
% 6.05/6.28      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 6.05/6.28         = (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 6.05/6.28      inference('demod', [status(thm)], ['43', '44'])).
% 6.05/6.28  thf('48', plain,
% 6.05/6.28      (![X0 : $i]:
% 6.05/6.28         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.28          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 6.05/6.28             (k1_tops_1 @ sk_A @ X0))
% 6.05/6.28          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))),
% 6.05/6.28      inference('demod', [status(thm)], ['40', '45', '46', '47'])).
% 6.05/6.28  thf('49', plain,
% 6.05/6.28      (((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 6.05/6.28         (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 6.05/6.28        | ~ (m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.05/6.28             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.05/6.28      inference('sup-', [status(thm)], ['27', '48'])).
% 6.05/6.28  thf('50', plain,
% 6.05/6.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf(dt_k2_pre_topc, axiom,
% 6.05/6.28    (![A:$i,B:$i]:
% 6.05/6.28     ( ( ( l1_pre_topc @ A ) & 
% 6.05/6.28         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.05/6.28       ( m1_subset_1 @
% 6.05/6.28         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 6.05/6.28  thf('51', plain,
% 6.05/6.28      (![X23 : $i, X24 : $i]:
% 6.05/6.28         (~ (l1_pre_topc @ X23)
% 6.05/6.28          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 6.05/6.28          | (m1_subset_1 @ (k2_pre_topc @ X23 @ X24) @ 
% 6.05/6.28             (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 6.05/6.28      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 6.05/6.28  thf('52', plain,
% 6.05/6.28      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.05/6.28         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.28        | ~ (l1_pre_topc @ sk_A))),
% 6.05/6.28      inference('sup-', [status(thm)], ['50', '51'])).
% 6.05/6.28  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('54', plain,
% 6.05/6.28      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.05/6.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('demod', [status(thm)], ['52', '53'])).
% 6.05/6.28  thf('55', plain,
% 6.05/6.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('56', plain,
% 6.05/6.28      (![X39 : $i, X40 : $i, X41 : $i]:
% 6.05/6.28         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 6.05/6.28          | ~ (r1_tarski @ X39 @ X41)
% 6.05/6.28          | (r1_tarski @ (k1_tops_1 @ X40 @ X39) @ (k1_tops_1 @ X40 @ X41))
% 6.05/6.28          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 6.05/6.28          | ~ (l1_pre_topc @ X40))),
% 6.05/6.28      inference('cnf', [status(esa)], [t48_tops_1])).
% 6.05/6.28  thf('57', plain,
% 6.05/6.28      (![X0 : $i]:
% 6.05/6.28         (~ (l1_pre_topc @ sk_A)
% 6.05/6.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.28          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 6.05/6.28          | ~ (r1_tarski @ sk_B @ X0))),
% 6.05/6.28      inference('sup-', [status(thm)], ['55', '56'])).
% 6.05/6.28  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('59', plain,
% 6.05/6.28      (![X0 : $i]:
% 6.05/6.28         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.28          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 6.05/6.28          | ~ (r1_tarski @ sk_B @ X0))),
% 6.05/6.28      inference('demod', [status(thm)], ['57', '58'])).
% 6.05/6.28  thf('60', plain,
% 6.05/6.28      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 6.05/6.28        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.28           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 6.05/6.28      inference('sup-', [status(thm)], ['54', '59'])).
% 6.05/6.28  thf('61', plain,
% 6.05/6.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf(t48_pre_topc, axiom,
% 6.05/6.28    (![A:$i]:
% 6.05/6.28     ( ( l1_pre_topc @ A ) =>
% 6.05/6.28       ( ![B:$i]:
% 6.05/6.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.05/6.28           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 6.05/6.28  thf('62', plain,
% 6.05/6.28      (![X25 : $i, X26 : $i]:
% 6.05/6.28         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 6.05/6.28          | (r1_tarski @ X25 @ (k2_pre_topc @ X26 @ X25))
% 6.05/6.28          | ~ (l1_pre_topc @ X26))),
% 6.05/6.28      inference('cnf', [status(esa)], [t48_pre_topc])).
% 6.05/6.28  thf('63', plain,
% 6.05/6.28      ((~ (l1_pre_topc @ sk_A)
% 6.05/6.28        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 6.05/6.28      inference('sup-', [status(thm)], ['61', '62'])).
% 6.05/6.28  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('65', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 6.05/6.28      inference('demod', [status(thm)], ['63', '64'])).
% 6.05/6.28  thf('66', plain,
% 6.05/6.28      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 6.05/6.28        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 6.05/6.28      inference('demod', [status(thm)], ['60', '65'])).
% 6.05/6.28  thf('67', plain,
% 6.05/6.28      (![X0 : $i, X2 : $i]:
% 6.05/6.28         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.05/6.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.05/6.28  thf('68', plain,
% 6.05/6.28      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.05/6.28           (k1_tops_1 @ sk_A @ sk_B))
% 6.05/6.28        | ((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 6.05/6.28            = (k1_tops_1 @ sk_A @ sk_B)))),
% 6.05/6.28      inference('sup-', [status(thm)], ['66', '67'])).
% 6.05/6.28  thf('69', plain,
% 6.05/6.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf(d6_tops_1, axiom,
% 6.05/6.28    (![A:$i]:
% 6.05/6.28     ( ( l1_pre_topc @ A ) =>
% 6.05/6.28       ( ![B:$i]:
% 6.05/6.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.05/6.28           ( ( v4_tops_1 @ B @ A ) <=>
% 6.05/6.28             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 6.05/6.28               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 6.05/6.28  thf('70', plain,
% 6.05/6.28      (![X27 : $i, X28 : $i]:
% 6.05/6.28         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 6.05/6.28          | ~ (v4_tops_1 @ X27 @ X28)
% 6.05/6.28          | (r1_tarski @ (k1_tops_1 @ X28 @ (k2_pre_topc @ X28 @ X27)) @ X27)
% 6.05/6.28          | ~ (l1_pre_topc @ X28))),
% 6.05/6.28      inference('cnf', [status(esa)], [d6_tops_1])).
% 6.05/6.28  thf('71', plain,
% 6.05/6.28      ((~ (l1_pre_topc @ sk_A)
% 6.05/6.28        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)
% 6.05/6.28        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 6.05/6.28      inference('sup-', [status(thm)], ['69', '70'])).
% 6.05/6.28  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('73', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('74', plain,
% 6.05/6.28      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)),
% 6.05/6.28      inference('demod', [status(thm)], ['71', '72', '73'])).
% 6.05/6.28  thf('75', plain,
% 6.05/6.28      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.05/6.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('demod', [status(thm)], ['52', '53'])).
% 6.05/6.28  thf('76', plain,
% 6.05/6.28      (![X29 : $i, X30 : $i]:
% 6.05/6.28         (~ (l1_pre_topc @ X29)
% 6.05/6.28          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 6.05/6.28          | (m1_subset_1 @ (k1_tops_1 @ X29 @ X30) @ 
% 6.05/6.28             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 6.05/6.28      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 6.05/6.28  thf('77', plain,
% 6.05/6.28      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.05/6.28         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.28        | ~ (l1_pre_topc @ sk_A))),
% 6.05/6.28      inference('sup-', [status(thm)], ['75', '76'])).
% 6.05/6.28  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('79', plain,
% 6.05/6.28      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.05/6.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('demod', [status(thm)], ['77', '78'])).
% 6.05/6.28  thf('80', plain,
% 6.05/6.28      (![X39 : $i, X40 : $i, X41 : $i]:
% 6.05/6.28         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 6.05/6.28          | ~ (r1_tarski @ X39 @ X41)
% 6.05/6.28          | (r1_tarski @ (k1_tops_1 @ X40 @ X39) @ (k1_tops_1 @ X40 @ X41))
% 6.05/6.28          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 6.05/6.28          | ~ (l1_pre_topc @ X40))),
% 6.05/6.28      inference('cnf', [status(esa)], [t48_tops_1])).
% 6.05/6.28  thf('81', plain,
% 6.05/6.28      (![X0 : $i]:
% 6.05/6.28         (~ (l1_pre_topc @ sk_A)
% 6.05/6.28          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.28          | (r1_tarski @ 
% 6.05/6.28             (k1_tops_1 @ sk_A @ 
% 6.05/6.28              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 6.05/6.28             (k1_tops_1 @ sk_A @ X0))
% 6.05/6.28          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.05/6.28               X0))),
% 6.05/6.28      inference('sup-', [status(thm)], ['79', '80'])).
% 6.05/6.28  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('83', plain,
% 6.05/6.28      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.05/6.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('demod', [status(thm)], ['52', '53'])).
% 6.05/6.28  thf('84', plain,
% 6.05/6.28      (![X35 : $i, X36 : $i]:
% 6.05/6.28         (~ (l1_pre_topc @ X35)
% 6.05/6.28          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 6.05/6.28          | ((k1_tops_1 @ X35 @ (k1_tops_1 @ X35 @ X36))
% 6.05/6.28              = (k1_tops_1 @ X35 @ X36)))),
% 6.05/6.28      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 6.05/6.28  thf('85', plain,
% 6.05/6.28      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 6.05/6.28          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 6.05/6.28        | ~ (l1_pre_topc @ sk_A))),
% 6.05/6.28      inference('sup-', [status(thm)], ['83', '84'])).
% 6.05/6.28  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('87', plain,
% 6.05/6.28      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 6.05/6.28         = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 6.05/6.28      inference('demod', [status(thm)], ['85', '86'])).
% 6.05/6.28  thf('88', plain,
% 6.05/6.28      (![X0 : $i]:
% 6.05/6.28         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.05/6.28          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.05/6.28             (k1_tops_1 @ sk_A @ X0))
% 6.05/6.28          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.05/6.28               X0))),
% 6.05/6.28      inference('demod', [status(thm)], ['81', '82', '87'])).
% 6.05/6.28  thf('89', plain,
% 6.05/6.28      (((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.05/6.28         (k1_tops_1 @ sk_A @ sk_B))
% 6.05/6.28        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 6.05/6.28      inference('sup-', [status(thm)], ['74', '88'])).
% 6.05/6.28  thf('90', plain,
% 6.05/6.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('91', plain,
% 6.05/6.28      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 6.05/6.28        (k1_tops_1 @ sk_A @ sk_B))),
% 6.05/6.28      inference('demod', [status(thm)], ['89', '90'])).
% 6.05/6.28  thf('92', plain,
% 6.05/6.28      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 6.05/6.28         = (k1_tops_1 @ sk_A @ sk_B))),
% 6.05/6.28      inference('demod', [status(thm)], ['68', '91'])).
% 6.05/6.28  thf('93', plain,
% 6.05/6.28      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 6.05/6.28        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('demod', [status(thm)], ['52', '53'])).
% 6.05/6.28  thf('94', plain,
% 6.05/6.28      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 6.05/6.28        (k1_tops_1 @ sk_A @ sk_B))),
% 6.05/6.28      inference('demod', [status(thm)], ['49', '92', '93'])).
% 6.05/6.28  thf(t67_xboole_1, axiom,
% 6.05/6.28    (![A:$i,B:$i,C:$i]:
% 6.05/6.28     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 6.05/6.28         ( r1_xboole_0 @ B @ C ) ) =>
% 6.05/6.28       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.05/6.28  thf('95', plain,
% 6.05/6.28      (![X14 : $i, X15 : $i, X16 : $i]:
% 6.05/6.28         (((X14) = (k1_xboole_0))
% 6.05/6.28          | ~ (r1_tarski @ X14 @ X15)
% 6.05/6.28          | ~ (r1_tarski @ X14 @ X16)
% 6.05/6.28          | ~ (r1_xboole_0 @ X15 @ X16))),
% 6.05/6.28      inference('cnf', [status(esa)], [t67_xboole_1])).
% 6.05/6.28  thf('96', plain,
% 6.05/6.28      (![X0 : $i]:
% 6.05/6.28         (~ (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 6.05/6.28          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 6.05/6.28          | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 6.05/6.28      inference('sup-', [status(thm)], ['94', '95'])).
% 6.05/6.28  thf('97', plain,
% 6.05/6.28      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('98', plain,
% 6.05/6.28      (![X0 : $i]:
% 6.05/6.28         (~ (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 6.05/6.28          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))),
% 6.05/6.28      inference('simplify_reflect-', [status(thm)], ['96', '97'])).
% 6.05/6.28  thf('99', plain,
% 6.05/6.28      (~ (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 6.05/6.28      inference('sup-', [status(thm)], ['8', '98'])).
% 6.05/6.28  thf('100', plain,
% 6.05/6.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf(t74_tops_1, axiom,
% 6.05/6.28    (![A:$i]:
% 6.05/6.28     ( ( l1_pre_topc @ A ) =>
% 6.05/6.28       ( ![B:$i]:
% 6.05/6.28         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.05/6.28           ( ( k1_tops_1 @ A @ B ) =
% 6.05/6.28             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 6.05/6.28  thf('101', plain,
% 6.05/6.28      (![X47 : $i, X48 : $i]:
% 6.05/6.28         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 6.05/6.28          | ((k1_tops_1 @ X48 @ X47)
% 6.05/6.28              = (k7_subset_1 @ (u1_struct_0 @ X48) @ X47 @ 
% 6.05/6.28                 (k2_tops_1 @ X48 @ X47)))
% 6.05/6.28          | ~ (l1_pre_topc @ X48))),
% 6.05/6.28      inference('cnf', [status(esa)], [t74_tops_1])).
% 6.05/6.28  thf('102', plain,
% 6.05/6.28      ((~ (l1_pre_topc @ sk_A)
% 6.05/6.28        | ((k1_tops_1 @ sk_A @ sk_B)
% 6.05/6.28            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 6.05/6.28               (k2_tops_1 @ sk_A @ sk_B))))),
% 6.05/6.28      inference('sup-', [status(thm)], ['100', '101'])).
% 6.05/6.28  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf('104', plain,
% 6.05/6.28      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.05/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.05/6.28  thf(redefinition_k7_subset_1, axiom,
% 6.05/6.28    (![A:$i,B:$i,C:$i]:
% 6.05/6.28     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.05/6.28       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 6.05/6.28  thf('105', plain,
% 6.05/6.28      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.05/6.28         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 6.05/6.28          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 6.05/6.28      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 6.05/6.28  thf('106', plain,
% 6.05/6.28      (![X0 : $i]:
% 6.05/6.28         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 6.05/6.28           = (k4_xboole_0 @ sk_B @ X0))),
% 6.05/6.28      inference('sup-', [status(thm)], ['104', '105'])).
% 6.05/6.28  thf('107', plain,
% 6.05/6.28      (((k1_tops_1 @ sk_A @ sk_B)
% 6.05/6.28         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 6.05/6.28      inference('demod', [status(thm)], ['102', '103', '106'])).
% 6.05/6.28  thf('108', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.05/6.28      inference('simplify', [status(thm)], ['19'])).
% 6.05/6.28  thf(t106_xboole_1, axiom,
% 6.05/6.28    (![A:$i,B:$i,C:$i]:
% 6.05/6.28     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 6.05/6.28       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 6.05/6.28  thf('109', plain,
% 6.05/6.28      (![X5 : $i, X6 : $i, X7 : $i]:
% 6.05/6.28         ((r1_xboole_0 @ X5 @ X7)
% 6.05/6.28          | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 6.05/6.28      inference('cnf', [status(esa)], [t106_xboole_1])).
% 6.05/6.28  thf('110', plain,
% 6.05/6.28      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 6.05/6.28      inference('sup-', [status(thm)], ['108', '109'])).
% 6.05/6.28  thf('111', plain,
% 6.05/6.28      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 6.05/6.28      inference('sup+', [status(thm)], ['107', '110'])).
% 6.05/6.28  thf('112', plain, ($false), inference('demod', [status(thm)], ['99', '111'])).
% 6.05/6.28  
% 6.05/6.28  % SZS output end Refutation
% 6.05/6.28  
% 6.05/6.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
