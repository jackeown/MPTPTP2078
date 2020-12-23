%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B3Zerquf0d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:59 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 948 expanded)
%              Number of leaves         :   22 ( 278 expanded)
%              Depth                    :   18
%              Number of atoms          : 1809 (12764 expanded)
%              Number of equality atoms :   29 (  72 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t111_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
           => ( ( v4_tops_1 @ ( k1_tops_1 @ A @ B ) @ A )
              & ( v4_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_tops_1 @ B @ A )
             => ( ( v4_tops_1 @ ( k1_tops_1 @ A @ B ) @ A )
                & ( v4_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t111_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d6_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
          <=> ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B )
              & ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X19 @ ( k2_pre_topc @ X19 @ X18 ) ) @ X18 )
      | ~ ( r1_tarski @ X18 @ ( k2_pre_topc @ X19 @ ( k1_tops_1 @ X19 @ X18 ) ) )
      | ( v4_tops_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k1_tops_1 @ X22 @ ( k1_tops_1 @ X22 @ X23 ) )
        = ( k1_tops_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('15',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('19',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('20',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('21',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ ( k2_pre_topc @ X16 @ X15 ) @ ( k2_pre_topc @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_tops_1 @ X18 @ X19 )
      | ( r1_tarski @ X18 @ ( k2_pre_topc @ X19 @ ( k1_tops_1 @ X19 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k2_pre_topc @ X11 @ ( k2_pre_topc @ X11 @ X12 ) )
        = ( k2_pre_topc @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('40',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','37','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ ( k2_pre_topc @ X16 @ X15 ) @ ( k2_pre_topc @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ X13 @ ( k2_pre_topc @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_tops_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ ( k2_pre_topc @ X19 @ X18 ) ) @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['64','65','66'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','69'])).

thf('71',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('73',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r1_tarski @ X24 @ X26 )
      | ( r1_tarski @ ( k1_tops_1 @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('79',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['70','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k2_pre_topc @ X11 @ ( k2_pre_topc @ X11 @ X12 ) )
        = ( k2_pre_topc @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('85',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['56','82','87'])).

thf('89',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','88'])).

thf('90',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['70','81'])).

thf('91',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('92',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','88'])).

thf('93',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('94',plain,
    ( ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','17','18','19','20','89','90','91','92','93'])).

thf('95',plain,
    ( ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['95'])).

thf('97',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('98',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X19 @ ( k2_pre_topc @ X19 @ X18 ) ) @ X18 )
      | ~ ( r1_tarski @ X18 @ ( k2_pre_topc @ X19 @ ( k1_tops_1 @ X19 @ X18 ) ) )
      | ( v4_tops_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('102',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','69'])).

thf('103',plain,
    ( ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('105',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('106',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('108',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('110',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('112',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('116',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('118',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ X13 @ ( k2_pre_topc @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('119',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('123',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('125',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k2_pre_topc @ X11 @ ( k2_pre_topc @ X11 @ X12 ) )
        = ( k2_pre_topc @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('126',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['116','123','128'])).

thf('130',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','88'])).

thf('131',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['103','131'])).

thf('133',plain,
    ( ~ ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['95'])).

thf('134',plain,(
    v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['95'])).

thf('136',plain,(
    ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['96','136'])).

thf('138',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['94','137'])).

thf('139',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('140',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('141',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r1_tarski @ X24 @ X26 )
      | ( r1_tarski @ ( k1_tops_1 @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('145',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k1_tops_1 @ X22 @ ( k1_tops_1 @ X22 @ X23 ) )
        = ( k1_tops_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('146',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['142','143','148'])).

thf('150',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['139','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    $false ),
    inference(demod,[status(thm)],['138','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B3Zerquf0d
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:34:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.91/1.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.11  % Solved by: fo/fo7.sh
% 0.91/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.11  % done 1703 iterations in 0.664s
% 0.91/1.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.11  % SZS output start Refutation
% 0.91/1.11  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.91/1.11  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.91/1.11  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.91/1.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.11  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.11  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.91/1.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.11  thf(t111_tops_1, conjecture,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( l1_pre_topc @ A ) =>
% 0.91/1.11       ( ![B:$i]:
% 0.91/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11           ( ( v4_tops_1 @ B @ A ) =>
% 0.91/1.11             ( ( v4_tops_1 @ ( k1_tops_1 @ A @ B ) @ A ) & 
% 0.91/1.11               ( v4_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ) ))).
% 0.91/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.11    (~( ![A:$i]:
% 0.91/1.11        ( ( l1_pre_topc @ A ) =>
% 0.91/1.11          ( ![B:$i]:
% 0.91/1.11            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11              ( ( v4_tops_1 @ B @ A ) =>
% 0.91/1.11                ( ( v4_tops_1 @ ( k1_tops_1 @ A @ B ) @ A ) & 
% 0.91/1.11                  ( v4_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ) ) )),
% 0.91/1.11    inference('cnf.neg', [status(esa)], [t111_tops_1])).
% 0.91/1.11  thf('0', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(dt_k1_tops_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( ( l1_pre_topc @ A ) & 
% 0.91/1.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.11       ( m1_subset_1 @
% 0.91/1.11         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.91/1.11  thf('1', plain,
% 0.91/1.11      (![X20 : $i, X21 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ X20)
% 0.91/1.11          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.91/1.11          | (m1_subset_1 @ (k1_tops_1 @ X20 @ X21) @ 
% 0.91/1.11             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 0.91/1.11      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.91/1.11  thf('2', plain,
% 0.91/1.11      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.11         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['0', '1'])).
% 0.91/1.11  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('4', plain,
% 0.91/1.11      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.11  thf('5', plain,
% 0.91/1.11      (![X20 : $i, X21 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ X20)
% 0.91/1.11          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.91/1.11          | (m1_subset_1 @ (k1_tops_1 @ X20 @ X21) @ 
% 0.91/1.11             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 0.91/1.11      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.91/1.11  thf('6', plain,
% 0.91/1.11      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.11         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.11  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('8', plain,
% 0.91/1.11      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['6', '7'])).
% 0.91/1.11  thf(d6_tops_1, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( l1_pre_topc @ A ) =>
% 0.91/1.11       ( ![B:$i]:
% 0.91/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11           ( ( v4_tops_1 @ B @ A ) <=>
% 0.91/1.11             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.91/1.11               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.91/1.11  thf('9', plain,
% 0.91/1.11      (![X18 : $i, X19 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.91/1.11          | ~ (r1_tarski @ (k1_tops_1 @ X19 @ (k2_pre_topc @ X19 @ X18)) @ X18)
% 0.91/1.11          | ~ (r1_tarski @ X18 @ (k2_pre_topc @ X19 @ (k1_tops_1 @ X19 @ X18)))
% 0.91/1.11          | (v4_tops_1 @ X18 @ X19)
% 0.91/1.11          | ~ (l1_pre_topc @ X19))),
% 0.91/1.11      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.91/1.11  thf('10', plain,
% 0.91/1.11      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.11        | (v4_tops_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.91/1.11        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ 
% 0.91/1.11              (k1_tops_1 @ sk_A @ 
% 0.91/1.11               (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))
% 0.91/1.11        | ~ (r1_tarski @ 
% 0.91/1.11             (k1_tops_1 @ sk_A @ 
% 0.91/1.11              (k2_pre_topc @ sk_A @ 
% 0.91/1.11               (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))) @ 
% 0.91/1.11             (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['8', '9'])).
% 0.91/1.11  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('12', plain,
% 0.91/1.11      (((v4_tops_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.91/1.11        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ 
% 0.91/1.11              (k1_tops_1 @ sk_A @ 
% 0.91/1.11               (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))
% 0.91/1.11        | ~ (r1_tarski @ 
% 0.91/1.11             (k1_tops_1 @ sk_A @ 
% 0.91/1.11              (k2_pre_topc @ sk_A @ 
% 0.91/1.11               (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))) @ 
% 0.91/1.11             (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.91/1.11      inference('demod', [status(thm)], ['10', '11'])).
% 0.91/1.11  thf('13', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(projectivity_k1_tops_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( ( l1_pre_topc @ A ) & 
% 0.91/1.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.11       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.91/1.11  thf('14', plain,
% 0.91/1.11      (![X22 : $i, X23 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ X22)
% 0.91/1.11          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.91/1.11          | ((k1_tops_1 @ X22 @ (k1_tops_1 @ X22 @ X23))
% 0.91/1.11              = (k1_tops_1 @ X22 @ X23)))),
% 0.91/1.11      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.91/1.11  thf('15', plain,
% 0.91/1.11      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.91/1.11          = (k1_tops_1 @ sk_A @ sk_B))
% 0.91/1.11        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['13', '14'])).
% 0.91/1.11  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('17', plain,
% 0.91/1.11      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.91/1.11         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.91/1.11  thf('18', plain,
% 0.91/1.11      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.91/1.11         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.91/1.11  thf('19', plain,
% 0.91/1.11      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.91/1.11         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.91/1.11  thf('20', plain,
% 0.91/1.11      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.91/1.11         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.91/1.11  thf('21', plain,
% 0.91/1.11      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.11  thf(dt_k2_pre_topc, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( ( l1_pre_topc @ A ) & 
% 0.91/1.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.11       ( m1_subset_1 @
% 0.91/1.11         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.91/1.11  thf('22', plain,
% 0.91/1.11      (![X9 : $i, X10 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ X9)
% 0.91/1.11          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.91/1.11          | (m1_subset_1 @ (k2_pre_topc @ X9 @ X10) @ 
% 0.91/1.11             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.91/1.11      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.91/1.11  thf('23', plain,
% 0.91/1.11      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.11         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['21', '22'])).
% 0.91/1.11  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('25', plain,
% 0.91/1.11      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['23', '24'])).
% 0.91/1.11  thf('26', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(t49_pre_topc, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( l1_pre_topc @ A ) =>
% 0.91/1.11       ( ![B:$i]:
% 0.91/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11           ( ![C:$i]:
% 0.91/1.11             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11               ( ( r1_tarski @ B @ C ) =>
% 0.91/1.11                 ( r1_tarski @
% 0.91/1.11                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.91/1.11  thf('27', plain,
% 0.91/1.11      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.91/1.11          | ~ (r1_tarski @ X15 @ X17)
% 0.91/1.11          | (r1_tarski @ (k2_pre_topc @ X16 @ X15) @ (k2_pre_topc @ X16 @ X17))
% 0.91/1.11          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.91/1.11          | ~ (l1_pre_topc @ X16))),
% 0.91/1.11      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.91/1.11  thf('28', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ sk_A)
% 0.91/1.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ X0))
% 0.91/1.11          | ~ (r1_tarski @ sk_B @ X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['26', '27'])).
% 0.91/1.11  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('30', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ X0))
% 0.91/1.11          | ~ (r1_tarski @ sk_B @ X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['28', '29'])).
% 0.91/1.11  thf('31', plain,
% 0.91/1.11      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.91/1.11        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.91/1.11           (k2_pre_topc @ sk_A @ 
% 0.91/1.11            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['25', '30'])).
% 0.91/1.11  thf('32', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('33', plain,
% 0.91/1.11      (![X18 : $i, X19 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.91/1.11          | ~ (v4_tops_1 @ X18 @ X19)
% 0.91/1.11          | (r1_tarski @ X18 @ (k2_pre_topc @ X19 @ (k1_tops_1 @ X19 @ X18)))
% 0.91/1.11          | ~ (l1_pre_topc @ X19))),
% 0.91/1.11      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.91/1.11  thf('34', plain,
% 0.91/1.11      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.11        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.91/1.11        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['32', '33'])).
% 0.91/1.11  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('36', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('37', plain,
% 0.91/1.11      ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.91/1.11  thf('38', plain,
% 0.91/1.11      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.11  thf(projectivity_k2_pre_topc, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( ( l1_pre_topc @ A ) & 
% 0.91/1.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.11       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.91/1.11         ( k2_pre_topc @ A @ B ) ) ))).
% 0.91/1.11  thf('39', plain,
% 0.91/1.11      (![X11 : $i, X12 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ X11)
% 0.91/1.11          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.91/1.11          | ((k2_pre_topc @ X11 @ (k2_pre_topc @ X11 @ X12))
% 0.91/1.11              = (k2_pre_topc @ X11 @ X12)))),
% 0.91/1.11      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.91/1.11  thf('40', plain,
% 0.91/1.11      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.91/1.11          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.91/1.11        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['38', '39'])).
% 0.91/1.11  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('42', plain,
% 0.91/1.11      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.91/1.11         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)], ['40', '41'])).
% 0.91/1.11  thf('43', plain,
% 0.91/1.11      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.91/1.11        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)], ['31', '37', '42'])).
% 0.91/1.11  thf(d10_xboole_0, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.11  thf('44', plain,
% 0.91/1.11      (![X0 : $i, X2 : $i]:
% 0.91/1.11         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.91/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.11  thf('45', plain,
% 0.91/1.11      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.11           (k2_pre_topc @ sk_A @ sk_B))
% 0.91/1.11        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.91/1.11            = (k2_pre_topc @ sk_A @ sk_B)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['43', '44'])).
% 0.91/1.11  thf('46', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('47', plain,
% 0.91/1.11      (![X9 : $i, X10 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ X9)
% 0.91/1.11          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.91/1.11          | (m1_subset_1 @ (k2_pre_topc @ X9 @ X10) @ 
% 0.91/1.11             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.91/1.11      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.91/1.11  thf('48', plain,
% 0.91/1.11      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.91/1.11         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['46', '47'])).
% 0.91/1.11  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('50', plain,
% 0.91/1.11      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['48', '49'])).
% 0.91/1.11  thf('51', plain,
% 0.91/1.11      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.11  thf('52', plain,
% 0.91/1.11      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.91/1.11          | ~ (r1_tarski @ X15 @ X17)
% 0.91/1.11          | (r1_tarski @ (k2_pre_topc @ X16 @ X15) @ (k2_pre_topc @ X16 @ X17))
% 0.91/1.11          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.91/1.11          | ~ (l1_pre_topc @ X16))),
% 0.91/1.11      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.91/1.11  thf('53', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ sk_A)
% 0.91/1.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ X0))
% 0.91/1.11          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['51', '52'])).
% 0.91/1.11  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('55', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ X0))
% 0.91/1.11          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['53', '54'])).
% 0.91/1.11  thf('56', plain,
% 0.91/1.11      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.91/1.11        | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.11           (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['50', '55'])).
% 0.91/1.11  thf('57', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(t48_pre_topc, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( l1_pre_topc @ A ) =>
% 0.91/1.11       ( ![B:$i]:
% 0.91/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.91/1.11  thf('58', plain,
% 0.91/1.11      (![X13 : $i, X14 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.91/1.11          | (r1_tarski @ X13 @ (k2_pre_topc @ X14 @ X13))
% 0.91/1.11          | ~ (l1_pre_topc @ X14))),
% 0.91/1.11      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.91/1.11  thf('59', plain,
% 0.91/1.11      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.11        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['57', '58'])).
% 0.91/1.11  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('61', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['59', '60'])).
% 0.91/1.11  thf('62', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('63', plain,
% 0.91/1.11      (![X18 : $i, X19 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.91/1.11          | ~ (v4_tops_1 @ X18 @ X19)
% 0.91/1.11          | (r1_tarski @ (k1_tops_1 @ X19 @ (k2_pre_topc @ X19 @ X18)) @ X18)
% 0.91/1.11          | ~ (l1_pre_topc @ X19))),
% 0.91/1.11      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.91/1.11  thf('64', plain,
% 0.91/1.11      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.11        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)
% 0.91/1.11        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['62', '63'])).
% 0.91/1.11  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('66', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('67', plain,
% 0.91/1.11      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)),
% 0.91/1.11      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.91/1.11  thf(t1_xboole_1, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i]:
% 0.91/1.11     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.91/1.11       ( r1_tarski @ A @ C ) ))).
% 0.91/1.11  thf('68', plain,
% 0.91/1.11      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.91/1.11         (~ (r1_tarski @ X3 @ X4)
% 0.91/1.11          | ~ (r1_tarski @ X4 @ X5)
% 0.91/1.11          | (r1_tarski @ X3 @ X5))),
% 0.91/1.11      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.91/1.11  thf('69', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ X0)
% 0.91/1.11          | ~ (r1_tarski @ sk_B @ X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['67', '68'])).
% 0.91/1.11  thf('70', plain,
% 0.91/1.11      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11        (k2_pre_topc @ sk_A @ sk_B))),
% 0.91/1.11      inference('sup-', [status(thm)], ['61', '69'])).
% 0.91/1.11  thf('71', plain,
% 0.91/1.11      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['48', '49'])).
% 0.91/1.11  thf('72', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(t48_tops_1, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( l1_pre_topc @ A ) =>
% 0.91/1.11       ( ![B:$i]:
% 0.91/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11           ( ![C:$i]:
% 0.91/1.11             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11               ( ( r1_tarski @ B @ C ) =>
% 0.91/1.11                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.91/1.11  thf('73', plain,
% 0.91/1.11      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.91/1.11          | ~ (r1_tarski @ X24 @ X26)
% 0.91/1.11          | (r1_tarski @ (k1_tops_1 @ X25 @ X24) @ (k1_tops_1 @ X25 @ X26))
% 0.91/1.11          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.91/1.11          | ~ (l1_pre_topc @ X25))),
% 0.91/1.11      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.91/1.11  thf('74', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ sk_A)
% 0.91/1.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.91/1.11          | ~ (r1_tarski @ sk_B @ X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['72', '73'])).
% 0.91/1.11  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('76', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.91/1.11          | ~ (r1_tarski @ sk_B @ X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['74', '75'])).
% 0.91/1.11  thf('77', plain,
% 0.91/1.11      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 0.91/1.11        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.11           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['71', '76'])).
% 0.91/1.11  thf('78', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['59', '60'])).
% 0.91/1.11  thf('79', plain,
% 0.91/1.11      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.11        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)], ['77', '78'])).
% 0.91/1.11  thf('80', plain,
% 0.91/1.11      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.91/1.11         (~ (r1_tarski @ X3 @ X4)
% 0.91/1.11          | ~ (r1_tarski @ X4 @ X5)
% 0.91/1.11          | (r1_tarski @ X3 @ X5))),
% 0.91/1.11      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.91/1.11  thf('81', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.91/1.11          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11               X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['79', '80'])).
% 0.91/1.11  thf('82', plain,
% 0.91/1.11      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.91/1.11      inference('sup-', [status(thm)], ['70', '81'])).
% 0.91/1.11  thf('83', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('84', plain,
% 0.91/1.11      (![X11 : $i, X12 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ X11)
% 0.91/1.11          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.91/1.11          | ((k2_pre_topc @ X11 @ (k2_pre_topc @ X11 @ X12))
% 0.91/1.11              = (k2_pre_topc @ X11 @ X12)))),
% 0.91/1.11      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.91/1.11  thf('85', plain,
% 0.91/1.11      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.91/1.11          = (k2_pre_topc @ sk_A @ sk_B))
% 0.91/1.11        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['83', '84'])).
% 0.91/1.11  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('87', plain,
% 0.91/1.11      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.91/1.11         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['85', '86'])).
% 0.91/1.11  thf('88', plain,
% 0.91/1.11      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.11        (k2_pre_topc @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['56', '82', '87'])).
% 0.91/1.11  thf('89', plain,
% 0.91/1.11      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.91/1.11         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['45', '88'])).
% 0.91/1.11  thf('90', plain,
% 0.91/1.11      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.91/1.11      inference('sup-', [status(thm)], ['70', '81'])).
% 0.91/1.11  thf('91', plain,
% 0.91/1.11      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.91/1.11         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.91/1.11  thf('92', plain,
% 0.91/1.11      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.91/1.11         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['45', '88'])).
% 0.91/1.11  thf('93', plain,
% 0.91/1.11      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.91/1.11         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.91/1.11  thf('94', plain,
% 0.91/1.11      (((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.91/1.11        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11             (k1_tops_1 @ sk_A @ sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)],
% 0.91/1.11                ['12', '17', '18', '19', '20', '89', '90', '91', '92', '93'])).
% 0.91/1.11  thf('95', plain,
% 0.91/1.11      ((~ (v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.91/1.11        | ~ (v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('96', plain,
% 0.91/1.11      ((~ (v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A))
% 0.91/1.11         <= (~ ((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)))),
% 0.91/1.11      inference('split', [status(esa)], ['95'])).
% 0.91/1.11  thf('97', plain,
% 0.91/1.11      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['48', '49'])).
% 0.91/1.11  thf('98', plain,
% 0.91/1.11      (![X18 : $i, X19 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.91/1.11          | ~ (r1_tarski @ (k1_tops_1 @ X19 @ (k2_pre_topc @ X19 @ X18)) @ X18)
% 0.91/1.11          | ~ (r1_tarski @ X18 @ (k2_pre_topc @ X19 @ (k1_tops_1 @ X19 @ X18)))
% 0.91/1.11          | (v4_tops_1 @ X18 @ X19)
% 0.91/1.11          | ~ (l1_pre_topc @ X19))),
% 0.91/1.11      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.91/1.11  thf('99', plain,
% 0.91/1.11      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.11        | (v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.91/1.11        | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ 
% 0.91/1.11              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.91/1.11        | ~ (r1_tarski @ 
% 0.91/1.11             (k1_tops_1 @ sk_A @ 
% 0.91/1.11              (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ sk_B)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['97', '98'])).
% 0.91/1.11  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('101', plain,
% 0.91/1.11      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.91/1.11         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['85', '86'])).
% 0.91/1.11  thf('102', plain,
% 0.91/1.11      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11        (k2_pre_topc @ sk_A @ sk_B))),
% 0.91/1.11      inference('sup-', [status(thm)], ['61', '69'])).
% 0.91/1.11  thf('103', plain,
% 0.91/1.11      (((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.91/1.11        | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ 
% 0.91/1.11              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.91/1.11      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 0.91/1.11  thf('104', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(t3_subset, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.91/1.11  thf('105', plain,
% 0.91/1.11      (![X6 : $i, X7 : $i]:
% 0.91/1.11         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.91/1.11      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.11  thf('106', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['104', '105'])).
% 0.91/1.11  thf('107', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ X0)
% 0.91/1.11          | ~ (r1_tarski @ sk_B @ X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['67', '68'])).
% 0.91/1.11  thf('108', plain,
% 0.91/1.11      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11        (u1_struct_0 @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['106', '107'])).
% 0.91/1.11  thf('109', plain,
% 0.91/1.11      (![X6 : $i, X8 : $i]:
% 0.91/1.11         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.91/1.11      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.11  thf('110', plain,
% 0.91/1.11      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['108', '109'])).
% 0.91/1.11  thf('111', plain,
% 0.91/1.11      (![X9 : $i, X10 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ X9)
% 0.91/1.11          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.91/1.11          | (m1_subset_1 @ (k2_pre_topc @ X9 @ X10) @ 
% 0.91/1.11             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.91/1.11      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.91/1.11  thf('112', plain,
% 0.91/1.11      (((m1_subset_1 @ 
% 0.91/1.11         (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 0.91/1.11         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['110', '111'])).
% 0.91/1.11  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('114', plain,
% 0.91/1.11      ((m1_subset_1 @ 
% 0.91/1.11        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['112', '113'])).
% 0.91/1.11  thf('115', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ X0))
% 0.91/1.11          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['53', '54'])).
% 0.91/1.11  thf('116', plain,
% 0.91/1.11      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.11           (k2_pre_topc @ sk_A @ 
% 0.91/1.11            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.91/1.11        | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.11           (k2_pre_topc @ sk_A @ 
% 0.91/1.11            (k2_pre_topc @ sk_A @ 
% 0.91/1.11             (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['114', '115'])).
% 0.91/1.11  thf('117', plain,
% 0.91/1.11      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['108', '109'])).
% 0.91/1.11  thf('118', plain,
% 0.91/1.11      (![X13 : $i, X14 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.91/1.11          | (r1_tarski @ X13 @ (k2_pre_topc @ X14 @ X13))
% 0.91/1.11          | ~ (l1_pre_topc @ X14))),
% 0.91/1.11      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.91/1.11  thf('119', plain,
% 0.91/1.11      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.11        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11           (k2_pre_topc @ sk_A @ 
% 0.91/1.11            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['117', '118'])).
% 0.91/1.11  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('121', plain,
% 0.91/1.11      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.91/1.11      inference('demod', [status(thm)], ['119', '120'])).
% 0.91/1.11  thf('122', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.91/1.11          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11               X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['79', '80'])).
% 0.91/1.11  thf('123', plain,
% 0.91/1.11      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.11        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['121', '122'])).
% 0.91/1.11  thf('124', plain,
% 0.91/1.11      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['108', '109'])).
% 0.91/1.11  thf('125', plain,
% 0.91/1.11      (![X11 : $i, X12 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ X11)
% 0.91/1.11          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.91/1.11          | ((k2_pre_topc @ X11 @ (k2_pre_topc @ X11 @ X12))
% 0.91/1.11              = (k2_pre_topc @ X11 @ X12)))),
% 0.91/1.11      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.91/1.11  thf('126', plain,
% 0.91/1.11      ((((k2_pre_topc @ sk_A @ 
% 0.91/1.11          (k2_pre_topc @ sk_A @ 
% 0.91/1.11           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.91/1.11          = (k2_pre_topc @ sk_A @ 
% 0.91/1.11             (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.91/1.11        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['124', '125'])).
% 0.91/1.11  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('128', plain,
% 0.91/1.11      (((k2_pre_topc @ sk_A @ 
% 0.91/1.11         (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.91/1.11         = (k2_pre_topc @ sk_A @ 
% 0.91/1.11            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.91/1.11      inference('demod', [status(thm)], ['126', '127'])).
% 0.91/1.11  thf('129', plain,
% 0.91/1.11      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.91/1.11        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.91/1.11      inference('demod', [status(thm)], ['116', '123', '128'])).
% 0.91/1.11  thf('130', plain,
% 0.91/1.11      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.91/1.11         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['45', '88'])).
% 0.91/1.11  thf('131', plain,
% 0.91/1.11      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.91/1.11        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.91/1.11      inference('demod', [status(thm)], ['129', '130'])).
% 0.91/1.11  thf('132', plain, ((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.91/1.11      inference('demod', [status(thm)], ['103', '131'])).
% 0.91/1.11  thf('133', plain,
% 0.91/1.11      ((~ (v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))
% 0.91/1.11         <= (~ ((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)))),
% 0.91/1.11      inference('split', [status(esa)], ['95'])).
% 0.91/1.11  thf('134', plain, (((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['132', '133'])).
% 0.91/1.11  thf('135', plain,
% 0.91/1.11      (~ ((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)) | 
% 0.91/1.11       ~ ((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.91/1.11      inference('split', [status(esa)], ['95'])).
% 0.91/1.11  thf('136', plain, (~ ((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A))),
% 0.91/1.11      inference('sat_resolution*', [status(thm)], ['134', '135'])).
% 0.91/1.11  thf('137', plain, (~ (v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.91/1.11      inference('simpl_trail', [status(thm)], ['96', '136'])).
% 0.91/1.11  thf('138', plain,
% 0.91/1.11      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11          (k1_tops_1 @ sk_A @ sk_B))),
% 0.91/1.11      inference('clc', [status(thm)], ['94', '137'])).
% 0.91/1.11  thf('139', plain,
% 0.91/1.11      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)),
% 0.91/1.11      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.91/1.11  thf('140', plain,
% 0.91/1.11      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['108', '109'])).
% 0.91/1.11  thf('141', plain,
% 0.91/1.11      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.91/1.11          | ~ (r1_tarski @ X24 @ X26)
% 0.91/1.11          | (r1_tarski @ (k1_tops_1 @ X25 @ X24) @ (k1_tops_1 @ X25 @ X26))
% 0.91/1.11          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.91/1.11          | ~ (l1_pre_topc @ X25))),
% 0.91/1.11      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.91/1.11  thf('142', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ sk_A)
% 0.91/1.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11          | (r1_tarski @ 
% 0.91/1.11             (k1_tops_1 @ sk_A @ 
% 0.91/1.11              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 0.91/1.11             (k1_tops_1 @ sk_A @ X0))
% 0.91/1.11          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11               X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['140', '141'])).
% 0.91/1.11  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('144', plain,
% 0.91/1.11      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['48', '49'])).
% 0.91/1.11  thf('145', plain,
% 0.91/1.11      (![X22 : $i, X23 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ X22)
% 0.91/1.11          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.91/1.11          | ((k1_tops_1 @ X22 @ (k1_tops_1 @ X22 @ X23))
% 0.91/1.11              = (k1_tops_1 @ X22 @ X23)))),
% 0.91/1.11      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.91/1.11  thf('146', plain,
% 0.91/1.11      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.91/1.11          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.91/1.11        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['144', '145'])).
% 0.91/1.11  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('148', plain,
% 0.91/1.11      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.91/1.11         = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)], ['146', '147'])).
% 0.91/1.11  thf('149', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11             (k1_tops_1 @ sk_A @ X0))
% 0.91/1.11          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11               X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['142', '143', '148'])).
% 0.91/1.11  thf('150', plain,
% 0.91/1.11      (((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11         (k1_tops_1 @ sk_A @ sk_B))
% 0.91/1.11        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['139', '149'])).
% 0.91/1.11  thf('151', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('152', plain,
% 0.91/1.11      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.91/1.11        (k1_tops_1 @ sk_A @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['150', '151'])).
% 0.91/1.11  thf('153', plain, ($false), inference('demod', [status(thm)], ['138', '152'])).
% 0.91/1.11  
% 0.91/1.11  % SZS output end Refutation
% 0.91/1.11  
% 0.96/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
