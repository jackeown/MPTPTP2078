%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NPUmnvSdsW

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:59 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 506 expanded)
%              Number of leaves         :   22 ( 149 expanded)
%              Depth                    :   19
%              Number of atoms          : 1604 (6863 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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

thf('0',plain,
    ( ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d6_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
          <=> ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B )
              & ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X17 @ ( k2_pre_topc @ X17 @ X16 ) ) @ X16 )
      | ~ ( r1_tarski @ X16 @ ( k2_pre_topc @ X17 @ ( k1_tops_1 @ X17 @ X16 ) ) )
      | ( v4_tops_1 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k2_pre_topc @ X11 @ ( k2_pre_topc @ X11 @ X12 ) )
        = ( k2_pre_topc @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('12',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X23 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_tops_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ ( k2_pre_topc @ X17 @ X16 ) ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ( r1_tarski @ ( k2_pre_topc @ X14 @ X13 ) @ ( k2_pre_topc @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ( r1_tarski @ ( k2_pre_topc @ X14 @ X13 ) @ ( k2_pre_topc @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_tops_1 @ X16 @ X17 )
      | ( r1_tarski @ X16 @ ( k2_pre_topc @ X17 @ ( k1_tops_1 @ X17 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('64',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k2_pre_topc @ X11 @ ( k2_pre_topc @ X11 @ X12 ) )
        = ( k2_pre_topc @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('65',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','67'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('73',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X23 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['70','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['44','80'])).

thf('82',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['35','81'])).

thf('83',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('84',plain,(
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

thf('85',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r1_tarski @ X24 @ X26 )
      | ( r1_tarski @ ( k1_tops_1 @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('91',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('92',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','94'])).

thf('96',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['82','95'])).

thf('97',plain,(
    v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['21','96'])).

thf('98',plain,
    ( ~ ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('99',plain,(
    v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v4_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,(
    ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('104',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X17 @ ( k2_pre_topc @ X17 @ X16 ) ) @ X16 )
      | ~ ( r1_tarski @ X16 @ ( k2_pre_topc @ X17 @ ( k1_tops_1 @ X17 @ X16 ) ) )
      | ( v4_tops_1 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('109',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k1_tops_1 @ X20 @ ( k1_tops_1 @ X20 @ X21 ) )
        = ( k1_tops_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('110',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('114',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('115',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,
    ( ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','112','117'])).

thf('119',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['70','79'])).

thf('120',plain,
    ( ( v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('122',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('123',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r1_tarski @ X24 @ X26 )
      | ( r1_tarski @ ( k1_tops_1 @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('127',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k1_tops_1 @ X20 @ ( k1_tops_1 @ X20 @ X21 ) )
        = ( k1_tops_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('128',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['124','125','130'])).

thf('132',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    v4_tops_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['120','134'])).

thf('136',plain,(
    $false ),
    inference(demod,[status(thm)],['102','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NPUmnvSdsW
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:49:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.71/1.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.71/1.95  % Solved by: fo/fo7.sh
% 1.71/1.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.71/1.95  % done 1546 iterations in 1.460s
% 1.71/1.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.71/1.95  % SZS output start Refutation
% 1.71/1.95  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.71/1.95  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 1.71/1.95  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.71/1.95  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.71/1.95  thf(sk_B_type, type, sk_B: $i).
% 1.71/1.95  thf(sk_A_type, type, sk_A: $i).
% 1.71/1.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.71/1.95  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.71/1.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.71/1.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.71/1.95  thf(t111_tops_1, conjecture,
% 1.71/1.95    (![A:$i]:
% 1.71/1.95     ( ( l1_pre_topc @ A ) =>
% 1.71/1.95       ( ![B:$i]:
% 1.71/1.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.71/1.95           ( ( v4_tops_1 @ B @ A ) =>
% 1.71/1.95             ( ( v4_tops_1 @ ( k1_tops_1 @ A @ B ) @ A ) & 
% 1.71/1.95               ( v4_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ) ))).
% 1.71/1.95  thf(zf_stmt_0, negated_conjecture,
% 1.71/1.95    (~( ![A:$i]:
% 1.71/1.95        ( ( l1_pre_topc @ A ) =>
% 1.71/1.95          ( ![B:$i]:
% 1.71/1.95            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.71/1.95              ( ( v4_tops_1 @ B @ A ) =>
% 1.71/1.95                ( ( v4_tops_1 @ ( k1_tops_1 @ A @ B ) @ A ) & 
% 1.71/1.95                  ( v4_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ) ) )),
% 1.71/1.95    inference('cnf.neg', [status(esa)], [t111_tops_1])).
% 1.71/1.95  thf('0', plain,
% 1.71/1.95      ((~ (v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.71/1.95        | ~ (v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('1', plain,
% 1.71/1.95      ((~ (v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A))
% 1.71/1.95         <= (~ ((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)))),
% 1.71/1.95      inference('split', [status(esa)], ['0'])).
% 1.71/1.95  thf('2', plain,
% 1.71/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf(dt_k2_pre_topc, axiom,
% 1.71/1.95    (![A:$i,B:$i]:
% 1.71/1.95     ( ( ( l1_pre_topc @ A ) & 
% 1.71/1.95         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.71/1.95       ( m1_subset_1 @
% 1.71/1.95         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.71/1.95  thf('3', plain,
% 1.71/1.95      (![X9 : $i, X10 : $i]:
% 1.71/1.95         (~ (l1_pre_topc @ X9)
% 1.71/1.95          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 1.71/1.95          | (m1_subset_1 @ (k2_pre_topc @ X9 @ X10) @ 
% 1.71/1.95             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 1.71/1.95      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.71/1.95  thf('4', plain,
% 1.71/1.95      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.71/1.95        | ~ (l1_pre_topc @ sk_A))),
% 1.71/1.95      inference('sup-', [status(thm)], ['2', '3'])).
% 1.71/1.95  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('6', plain,
% 1.71/1.95      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('demod', [status(thm)], ['4', '5'])).
% 1.71/1.95  thf(d6_tops_1, axiom,
% 1.71/1.95    (![A:$i]:
% 1.71/1.95     ( ( l1_pre_topc @ A ) =>
% 1.71/1.95       ( ![B:$i]:
% 1.71/1.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.71/1.95           ( ( v4_tops_1 @ B @ A ) <=>
% 1.71/1.95             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 1.71/1.95               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 1.71/1.95  thf('7', plain,
% 1.71/1.95      (![X16 : $i, X17 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.71/1.95          | ~ (r1_tarski @ (k1_tops_1 @ X17 @ (k2_pre_topc @ X17 @ X16)) @ X16)
% 1.71/1.95          | ~ (r1_tarski @ X16 @ (k2_pre_topc @ X17 @ (k1_tops_1 @ X17 @ X16)))
% 1.71/1.95          | (v4_tops_1 @ X16 @ X17)
% 1.71/1.95          | ~ (l1_pre_topc @ X17))),
% 1.71/1.95      inference('cnf', [status(esa)], [d6_tops_1])).
% 1.71/1.95  thf('8', plain,
% 1.71/1.95      ((~ (l1_pre_topc @ sk_A)
% 1.71/1.95        | (v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.71/1.95        | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95             (k2_pre_topc @ sk_A @ 
% 1.71/1.95              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 1.71/1.95        | ~ (r1_tarski @ 
% 1.71/1.95             (k1_tops_1 @ sk_A @ 
% 1.71/1.95              (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 1.71/1.95             (k2_pre_topc @ sk_A @ sk_B)))),
% 1.71/1.95      inference('sup-', [status(thm)], ['6', '7'])).
% 1.71/1.95  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('10', plain,
% 1.71/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf(projectivity_k2_pre_topc, axiom,
% 1.71/1.95    (![A:$i,B:$i]:
% 1.71/1.95     ( ( ( l1_pre_topc @ A ) & 
% 1.71/1.95         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.71/1.95       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 1.71/1.95         ( k2_pre_topc @ A @ B ) ) ))).
% 1.71/1.95  thf('11', plain,
% 1.71/1.95      (![X11 : $i, X12 : $i]:
% 1.71/1.95         (~ (l1_pre_topc @ X11)
% 1.71/1.95          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 1.71/1.95          | ((k2_pre_topc @ X11 @ (k2_pre_topc @ X11 @ X12))
% 1.71/1.95              = (k2_pre_topc @ X11 @ X12)))),
% 1.71/1.95      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 1.71/1.95  thf('12', plain,
% 1.71/1.95      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 1.71/1.95          = (k2_pre_topc @ sk_A @ sk_B))
% 1.71/1.95        | ~ (l1_pre_topc @ sk_A))),
% 1.71/1.95      inference('sup-', [status(thm)], ['10', '11'])).
% 1.71/1.95  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('14', plain,
% 1.71/1.95      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 1.71/1.95         = (k2_pre_topc @ sk_A @ sk_B))),
% 1.71/1.95      inference('demod', [status(thm)], ['12', '13'])).
% 1.71/1.95  thf('15', plain,
% 1.71/1.95      (((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.71/1.95        | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95             (k2_pre_topc @ sk_A @ 
% 1.71/1.95              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 1.71/1.95        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.71/1.95             (k2_pre_topc @ sk_A @ sk_B)))),
% 1.71/1.95      inference('demod', [status(thm)], ['8', '9', '14'])).
% 1.71/1.95  thf('16', plain,
% 1.71/1.95      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('demod', [status(thm)], ['4', '5'])).
% 1.71/1.95  thf(t44_tops_1, axiom,
% 1.71/1.95    (![A:$i]:
% 1.71/1.95     ( ( l1_pre_topc @ A ) =>
% 1.71/1.95       ( ![B:$i]:
% 1.71/1.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.71/1.95           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.71/1.95  thf('17', plain,
% 1.71/1.95      (![X22 : $i, X23 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.71/1.95          | (r1_tarski @ (k1_tops_1 @ X23 @ X22) @ X22)
% 1.71/1.95          | ~ (l1_pre_topc @ X23))),
% 1.71/1.95      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.71/1.95  thf('18', plain,
% 1.71/1.95      ((~ (l1_pre_topc @ sk_A)
% 1.71/1.95        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.71/1.95           (k2_pre_topc @ sk_A @ sk_B)))),
% 1.71/1.95      inference('sup-', [status(thm)], ['16', '17'])).
% 1.71/1.95  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('20', plain,
% 1.71/1.95      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.71/1.95        (k2_pre_topc @ sk_A @ sk_B))),
% 1.71/1.95      inference('demod', [status(thm)], ['18', '19'])).
% 1.71/1.95  thf('21', plain,
% 1.71/1.95      (((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.71/1.95        | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95             (k2_pre_topc @ sk_A @ 
% 1.71/1.95              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 1.71/1.95      inference('demod', [status(thm)], ['15', '20'])).
% 1.71/1.95  thf('22', plain,
% 1.71/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf(t3_subset, axiom,
% 1.71/1.95    (![A:$i,B:$i]:
% 1.71/1.95     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.71/1.95  thf('23', plain,
% 1.71/1.95      (![X6 : $i, X7 : $i]:
% 1.71/1.95         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.71/1.95      inference('cnf', [status(esa)], [t3_subset])).
% 1.71/1.95  thf('24', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.71/1.95      inference('sup-', [status(thm)], ['22', '23'])).
% 1.71/1.95  thf('25', plain,
% 1.71/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('26', plain,
% 1.71/1.95      (![X16 : $i, X17 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.71/1.95          | ~ (v4_tops_1 @ X16 @ X17)
% 1.71/1.95          | (r1_tarski @ (k1_tops_1 @ X17 @ (k2_pre_topc @ X17 @ X16)) @ X16)
% 1.71/1.95          | ~ (l1_pre_topc @ X17))),
% 1.71/1.95      inference('cnf', [status(esa)], [d6_tops_1])).
% 1.71/1.95  thf('27', plain,
% 1.71/1.95      ((~ (l1_pre_topc @ sk_A)
% 1.71/1.95        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)
% 1.71/1.95        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 1.71/1.95      inference('sup-', [status(thm)], ['25', '26'])).
% 1.71/1.95  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('29', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('30', plain,
% 1.71/1.95      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)),
% 1.71/1.95      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.71/1.95  thf(t1_xboole_1, axiom,
% 1.71/1.95    (![A:$i,B:$i,C:$i]:
% 1.71/1.95     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.71/1.95       ( r1_tarski @ A @ C ) ))).
% 1.71/1.95  thf('31', plain,
% 1.71/1.95      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.71/1.95         (~ (r1_tarski @ X3 @ X4)
% 1.71/1.95          | ~ (r1_tarski @ X4 @ X5)
% 1.71/1.95          | (r1_tarski @ X3 @ X5))),
% 1.71/1.95      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.71/1.95  thf('32', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ X0)
% 1.71/1.95          | ~ (r1_tarski @ sk_B @ X0))),
% 1.71/1.95      inference('sup-', [status(thm)], ['30', '31'])).
% 1.71/1.95  thf('33', plain,
% 1.71/1.95      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.71/1.95        (u1_struct_0 @ sk_A))),
% 1.71/1.95      inference('sup-', [status(thm)], ['24', '32'])).
% 1.71/1.95  thf('34', plain,
% 1.71/1.95      (![X6 : $i, X8 : $i]:
% 1.71/1.95         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 1.71/1.95      inference('cnf', [status(esa)], [t3_subset])).
% 1.71/1.95  thf('35', plain,
% 1.71/1.95      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.71/1.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('sup-', [status(thm)], ['33', '34'])).
% 1.71/1.95  thf('36', plain,
% 1.71/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf(dt_k1_tops_1, axiom,
% 1.71/1.95    (![A:$i,B:$i]:
% 1.71/1.95     ( ( ( l1_pre_topc @ A ) & 
% 1.71/1.95         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.71/1.95       ( m1_subset_1 @
% 1.71/1.95         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.71/1.95  thf('37', plain,
% 1.71/1.95      (![X18 : $i, X19 : $i]:
% 1.71/1.95         (~ (l1_pre_topc @ X18)
% 1.71/1.95          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.71/1.95          | (m1_subset_1 @ (k1_tops_1 @ X18 @ X19) @ 
% 1.71/1.95             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 1.71/1.95      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.71/1.95  thf('38', plain,
% 1.71/1.95      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.71/1.95         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.71/1.95        | ~ (l1_pre_topc @ sk_A))),
% 1.71/1.95      inference('sup-', [status(thm)], ['36', '37'])).
% 1.71/1.95  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('40', plain,
% 1.71/1.95      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.71/1.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('demod', [status(thm)], ['38', '39'])).
% 1.71/1.95  thf(t49_pre_topc, axiom,
% 1.71/1.95    (![A:$i]:
% 1.71/1.95     ( ( l1_pre_topc @ A ) =>
% 1.71/1.95       ( ![B:$i]:
% 1.71/1.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.71/1.95           ( ![C:$i]:
% 1.71/1.95             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.71/1.95               ( ( r1_tarski @ B @ C ) =>
% 1.71/1.95                 ( r1_tarski @
% 1.71/1.95                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 1.71/1.95  thf('41', plain,
% 1.71/1.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.71/1.95          | ~ (r1_tarski @ X13 @ X15)
% 1.71/1.95          | (r1_tarski @ (k2_pre_topc @ X14 @ X13) @ (k2_pre_topc @ X14 @ X15))
% 1.71/1.95          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.71/1.95          | ~ (l1_pre_topc @ X14))),
% 1.71/1.95      inference('cnf', [status(esa)], [t49_pre_topc])).
% 1.71/1.95  thf('42', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         (~ (l1_pre_topc @ sk_A)
% 1.71/1.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.71/1.95          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.71/1.95             (k2_pre_topc @ sk_A @ X0))
% 1.71/1.95          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 1.71/1.95      inference('sup-', [status(thm)], ['40', '41'])).
% 1.71/1.95  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('44', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.71/1.95          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.71/1.95             (k2_pre_topc @ sk_A @ X0))
% 1.71/1.95          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 1.71/1.95      inference('demod', [status(thm)], ['42', '43'])).
% 1.71/1.95  thf('45', plain,
% 1.71/1.95      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.71/1.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('demod', [status(thm)], ['38', '39'])).
% 1.71/1.95  thf('46', plain,
% 1.71/1.95      (![X9 : $i, X10 : $i]:
% 1.71/1.95         (~ (l1_pre_topc @ X9)
% 1.71/1.95          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 1.71/1.95          | (m1_subset_1 @ (k2_pre_topc @ X9 @ X10) @ 
% 1.71/1.95             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 1.71/1.95      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.71/1.95  thf('47', plain,
% 1.71/1.95      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.71/1.95         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.71/1.95        | ~ (l1_pre_topc @ sk_A))),
% 1.71/1.95      inference('sup-', [status(thm)], ['45', '46'])).
% 1.71/1.95  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('49', plain,
% 1.71/1.95      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.71/1.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('demod', [status(thm)], ['47', '48'])).
% 1.71/1.95  thf('50', plain,
% 1.71/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('51', plain,
% 1.71/1.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.71/1.95          | ~ (r1_tarski @ X13 @ X15)
% 1.71/1.95          | (r1_tarski @ (k2_pre_topc @ X14 @ X13) @ (k2_pre_topc @ X14 @ X15))
% 1.71/1.95          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.71/1.95          | ~ (l1_pre_topc @ X14))),
% 1.71/1.95      inference('cnf', [status(esa)], [t49_pre_topc])).
% 1.71/1.95  thf('52', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         (~ (l1_pre_topc @ sk_A)
% 1.71/1.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.71/1.95          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95             (k2_pre_topc @ sk_A @ X0))
% 1.71/1.95          | ~ (r1_tarski @ sk_B @ X0))),
% 1.71/1.95      inference('sup-', [status(thm)], ['50', '51'])).
% 1.71/1.95  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('54', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.71/1.95          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95             (k2_pre_topc @ sk_A @ X0))
% 1.71/1.95          | ~ (r1_tarski @ sk_B @ X0))),
% 1.71/1.95      inference('demod', [status(thm)], ['52', '53'])).
% 1.71/1.95  thf('55', plain,
% 1.71/1.95      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.71/1.95        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95           (k2_pre_topc @ sk_A @ 
% 1.71/1.95            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.71/1.95      inference('sup-', [status(thm)], ['49', '54'])).
% 1.71/1.95  thf('56', plain,
% 1.71/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('57', plain,
% 1.71/1.95      (![X16 : $i, X17 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.71/1.95          | ~ (v4_tops_1 @ X16 @ X17)
% 1.71/1.95          | (r1_tarski @ X16 @ (k2_pre_topc @ X17 @ (k1_tops_1 @ X17 @ X16)))
% 1.71/1.95          | ~ (l1_pre_topc @ X17))),
% 1.71/1.95      inference('cnf', [status(esa)], [d6_tops_1])).
% 1.71/1.95  thf('58', plain,
% 1.71/1.95      ((~ (l1_pre_topc @ sk_A)
% 1.71/1.95        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.71/1.95        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 1.71/1.95      inference('sup-', [status(thm)], ['56', '57'])).
% 1.71/1.95  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('60', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('61', plain,
% 1.71/1.95      ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.71/1.95      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.71/1.95  thf('62', plain,
% 1.71/1.95      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95        (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.71/1.95      inference('demod', [status(thm)], ['55', '61'])).
% 1.71/1.95  thf('63', plain,
% 1.71/1.95      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.71/1.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('demod', [status(thm)], ['38', '39'])).
% 1.71/1.95  thf('64', plain,
% 1.71/1.95      (![X11 : $i, X12 : $i]:
% 1.71/1.95         (~ (l1_pre_topc @ X11)
% 1.71/1.95          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 1.71/1.95          | ((k2_pre_topc @ X11 @ (k2_pre_topc @ X11 @ X12))
% 1.71/1.95              = (k2_pre_topc @ X11 @ X12)))),
% 1.71/1.95      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 1.71/1.95  thf('65', plain,
% 1.71/1.95      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.71/1.95          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.71/1.95        | ~ (l1_pre_topc @ sk_A))),
% 1.71/1.95      inference('sup-', [status(thm)], ['63', '64'])).
% 1.71/1.95  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('67', plain,
% 1.71/1.95      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.71/1.95         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.71/1.95      inference('demod', [status(thm)], ['65', '66'])).
% 1.71/1.95  thf('68', plain,
% 1.71/1.95      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.71/1.95      inference('demod', [status(thm)], ['62', '67'])).
% 1.71/1.95  thf(d10_xboole_0, axiom,
% 1.71/1.95    (![A:$i,B:$i]:
% 1.71/1.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.71/1.95  thf('69', plain,
% 1.71/1.95      (![X0 : $i, X2 : $i]:
% 1.71/1.95         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.71/1.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.71/1.95  thf('70', plain,
% 1.71/1.95      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.71/1.95           (k2_pre_topc @ sk_A @ sk_B))
% 1.71/1.95        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.71/1.95            = (k2_pre_topc @ sk_A @ sk_B)))),
% 1.71/1.95      inference('sup-', [status(thm)], ['68', '69'])).
% 1.71/1.95  thf('71', plain,
% 1.71/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('72', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.71/1.95          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.71/1.95             (k2_pre_topc @ sk_A @ X0))
% 1.71/1.95          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 1.71/1.95      inference('demod', [status(thm)], ['42', '43'])).
% 1.71/1.95  thf('73', plain,
% 1.71/1.95      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.71/1.95        | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.71/1.95           (k2_pre_topc @ sk_A @ sk_B)))),
% 1.71/1.95      inference('sup-', [status(thm)], ['71', '72'])).
% 1.71/1.95  thf('74', plain,
% 1.71/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('75', plain,
% 1.71/1.95      (![X22 : $i, X23 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.71/1.95          | (r1_tarski @ (k1_tops_1 @ X23 @ X22) @ X22)
% 1.71/1.95          | ~ (l1_pre_topc @ X23))),
% 1.71/1.95      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.71/1.95  thf('76', plain,
% 1.71/1.95      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.71/1.95      inference('sup-', [status(thm)], ['74', '75'])).
% 1.71/1.95  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('78', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.71/1.95      inference('demod', [status(thm)], ['76', '77'])).
% 1.71/1.95  thf('79', plain,
% 1.71/1.95      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.71/1.95        (k2_pre_topc @ sk_A @ sk_B))),
% 1.71/1.95      inference('demod', [status(thm)], ['73', '78'])).
% 1.71/1.95  thf('80', plain,
% 1.71/1.95      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.71/1.95         = (k2_pre_topc @ sk_A @ sk_B))),
% 1.71/1.95      inference('demod', [status(thm)], ['70', '79'])).
% 1.71/1.95  thf('81', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.71/1.95          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95             (k2_pre_topc @ sk_A @ X0))
% 1.71/1.95          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 1.71/1.95      inference('demod', [status(thm)], ['44', '80'])).
% 1.71/1.95  thf('82', plain,
% 1.71/1.95      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.71/1.95           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 1.71/1.95        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95           (k2_pre_topc @ sk_A @ 
% 1.71/1.95            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 1.71/1.95      inference('sup-', [status(thm)], ['35', '81'])).
% 1.71/1.95  thf('83', plain,
% 1.71/1.95      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('demod', [status(thm)], ['4', '5'])).
% 1.71/1.95  thf('84', plain,
% 1.71/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf(t48_tops_1, axiom,
% 1.71/1.95    (![A:$i]:
% 1.71/1.95     ( ( l1_pre_topc @ A ) =>
% 1.71/1.95       ( ![B:$i]:
% 1.71/1.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.71/1.95           ( ![C:$i]:
% 1.71/1.95             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.71/1.95               ( ( r1_tarski @ B @ C ) =>
% 1.71/1.95                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.71/1.95  thf('85', plain,
% 1.71/1.95      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.71/1.95          | ~ (r1_tarski @ X24 @ X26)
% 1.71/1.95          | (r1_tarski @ (k1_tops_1 @ X25 @ X24) @ (k1_tops_1 @ X25 @ X26))
% 1.71/1.95          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.71/1.95          | ~ (l1_pre_topc @ X25))),
% 1.71/1.95      inference('cnf', [status(esa)], [t48_tops_1])).
% 1.71/1.95  thf('86', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         (~ (l1_pre_topc @ sk_A)
% 1.71/1.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.71/1.95          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 1.71/1.95          | ~ (r1_tarski @ sk_B @ X0))),
% 1.71/1.95      inference('sup-', [status(thm)], ['84', '85'])).
% 1.71/1.95  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('88', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.71/1.95          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 1.71/1.95          | ~ (r1_tarski @ sk_B @ X0))),
% 1.71/1.95      inference('demod', [status(thm)], ['86', '87'])).
% 1.71/1.95  thf('89', plain,
% 1.71/1.95      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 1.71/1.95        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.71/1.95           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 1.71/1.95      inference('sup-', [status(thm)], ['83', '88'])).
% 1.71/1.95  thf('90', plain,
% 1.71/1.95      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.71/1.95        (k2_pre_topc @ sk_A @ sk_B))),
% 1.71/1.95      inference('demod', [status(thm)], ['73', '78'])).
% 1.71/1.95  thf('91', plain,
% 1.71/1.95      ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.71/1.95      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.71/1.95  thf('92', plain,
% 1.71/1.95      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.71/1.95         (~ (r1_tarski @ X3 @ X4)
% 1.71/1.95          | ~ (r1_tarski @ X4 @ X5)
% 1.71/1.95          | (r1_tarski @ X3 @ X5))),
% 1.71/1.95      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.71/1.95  thf('93', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         ((r1_tarski @ sk_B @ X0)
% 1.71/1.95          | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.71/1.95               X0))),
% 1.71/1.95      inference('sup-', [status(thm)], ['91', '92'])).
% 1.71/1.95  thf('94', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 1.71/1.95      inference('sup-', [status(thm)], ['90', '93'])).
% 1.71/1.95  thf('95', plain,
% 1.71/1.95      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.71/1.95        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.71/1.95      inference('demod', [status(thm)], ['89', '94'])).
% 1.71/1.95  thf('96', plain,
% 1.71/1.95      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 1.71/1.95      inference('demod', [status(thm)], ['82', '95'])).
% 1.71/1.95  thf('97', plain, ((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.71/1.95      inference('demod', [status(thm)], ['21', '96'])).
% 1.71/1.95  thf('98', plain,
% 1.71/1.95      ((~ (v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))
% 1.71/1.95         <= (~ ((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)))),
% 1.71/1.95      inference('split', [status(esa)], ['0'])).
% 1.71/1.95  thf('99', plain, (((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 1.71/1.95      inference('sup-', [status(thm)], ['97', '98'])).
% 1.71/1.95  thf('100', plain,
% 1.71/1.95      (~ ((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)) | 
% 1.71/1.95       ~ ((v4_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 1.71/1.95      inference('split', [status(esa)], ['0'])).
% 1.71/1.95  thf('101', plain, (~ ((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A))),
% 1.71/1.95      inference('sat_resolution*', [status(thm)], ['99', '100'])).
% 1.71/1.95  thf('102', plain, (~ (v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.71/1.95      inference('simpl_trail', [status(thm)], ['1', '101'])).
% 1.71/1.95  thf('103', plain,
% 1.71/1.95      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.71/1.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('demod', [status(thm)], ['38', '39'])).
% 1.71/1.95  thf('104', plain,
% 1.71/1.95      (![X16 : $i, X17 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.71/1.95          | ~ (r1_tarski @ (k1_tops_1 @ X17 @ (k2_pre_topc @ X17 @ X16)) @ X16)
% 1.71/1.95          | ~ (r1_tarski @ X16 @ (k2_pre_topc @ X17 @ (k1_tops_1 @ X17 @ X16)))
% 1.71/1.95          | (v4_tops_1 @ X16 @ X17)
% 1.71/1.95          | ~ (l1_pre_topc @ X17))),
% 1.71/1.95      inference('cnf', [status(esa)], [d6_tops_1])).
% 1.71/1.95  thf('105', plain,
% 1.71/1.95      ((~ (l1_pre_topc @ sk_A)
% 1.71/1.95        | (v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.71/1.95        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.71/1.95             (k2_pre_topc @ sk_A @ 
% 1.71/1.95              (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.71/1.95        | ~ (r1_tarski @ 
% 1.71/1.95             (k1_tops_1 @ sk_A @ 
% 1.71/1.95              (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 1.71/1.95             (k1_tops_1 @ sk_A @ sk_B)))),
% 1.71/1.95      inference('sup-', [status(thm)], ['103', '104'])).
% 1.71/1.95  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('107', plain,
% 1.71/1.95      (((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.71/1.95        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.71/1.95             (k2_pre_topc @ sk_A @ 
% 1.71/1.95              (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.71/1.95        | ~ (r1_tarski @ 
% 1.71/1.95             (k1_tops_1 @ sk_A @ 
% 1.71/1.95              (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 1.71/1.95             (k1_tops_1 @ sk_A @ sk_B)))),
% 1.71/1.95      inference('demod', [status(thm)], ['105', '106'])).
% 1.71/1.95  thf('108', plain,
% 1.71/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf(projectivity_k1_tops_1, axiom,
% 1.71/1.95    (![A:$i,B:$i]:
% 1.71/1.95     ( ( ( l1_pre_topc @ A ) & 
% 1.71/1.95         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.71/1.95       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 1.71/1.95  thf('109', plain,
% 1.71/1.95      (![X20 : $i, X21 : $i]:
% 1.71/1.95         (~ (l1_pre_topc @ X20)
% 1.71/1.95          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.71/1.95          | ((k1_tops_1 @ X20 @ (k1_tops_1 @ X20 @ X21))
% 1.71/1.95              = (k1_tops_1 @ X20 @ X21)))),
% 1.71/1.95      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 1.71/1.95  thf('110', plain,
% 1.71/1.95      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.71/1.95          = (k1_tops_1 @ sk_A @ sk_B))
% 1.71/1.95        | ~ (l1_pre_topc @ sk_A))),
% 1.71/1.95      inference('sup-', [status(thm)], ['108', '109'])).
% 1.71/1.95  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('112', plain,
% 1.71/1.95      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.71/1.95         = (k1_tops_1 @ sk_A @ sk_B))),
% 1.71/1.95      inference('demod', [status(thm)], ['110', '111'])).
% 1.71/1.95  thf('113', plain,
% 1.71/1.95      ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.71/1.95      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.71/1.95  thf('114', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.71/1.95      inference('demod', [status(thm)], ['76', '77'])).
% 1.71/1.95  thf('115', plain,
% 1.71/1.95      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.71/1.95         (~ (r1_tarski @ X3 @ X4)
% 1.71/1.95          | ~ (r1_tarski @ X4 @ X5)
% 1.71/1.95          | (r1_tarski @ X3 @ X5))),
% 1.71/1.95      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.71/1.95  thf('116', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.71/1.95          | ~ (r1_tarski @ sk_B @ X0))),
% 1.71/1.95      inference('sup-', [status(thm)], ['114', '115'])).
% 1.71/1.95  thf('117', plain,
% 1.71/1.95      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.71/1.95        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.71/1.95      inference('sup-', [status(thm)], ['113', '116'])).
% 1.71/1.95  thf('118', plain,
% 1.71/1.95      (((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.71/1.95        | ~ (r1_tarski @ 
% 1.71/1.95             (k1_tops_1 @ sk_A @ 
% 1.71/1.95              (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 1.71/1.95             (k1_tops_1 @ sk_A @ sk_B)))),
% 1.71/1.95      inference('demod', [status(thm)], ['107', '112', '117'])).
% 1.71/1.95  thf('119', plain,
% 1.71/1.95      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.71/1.95         = (k2_pre_topc @ sk_A @ sk_B))),
% 1.71/1.95      inference('demod', [status(thm)], ['70', '79'])).
% 1.71/1.95  thf('120', plain,
% 1.71/1.95      (((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.71/1.95        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.71/1.95             (k1_tops_1 @ sk_A @ sk_B)))),
% 1.71/1.95      inference('demod', [status(thm)], ['118', '119'])).
% 1.71/1.95  thf('121', plain,
% 1.71/1.95      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)),
% 1.71/1.95      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.71/1.95  thf('122', plain,
% 1.71/1.95      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.71/1.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('sup-', [status(thm)], ['33', '34'])).
% 1.71/1.95  thf('123', plain,
% 1.71/1.95      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.71/1.95          | ~ (r1_tarski @ X24 @ X26)
% 1.71/1.95          | (r1_tarski @ (k1_tops_1 @ X25 @ X24) @ (k1_tops_1 @ X25 @ X26))
% 1.71/1.95          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.71/1.95          | ~ (l1_pre_topc @ X25))),
% 1.71/1.95      inference('cnf', [status(esa)], [t48_tops_1])).
% 1.71/1.95  thf('124', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         (~ (l1_pre_topc @ sk_A)
% 1.71/1.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.71/1.95          | (r1_tarski @ 
% 1.71/1.95             (k1_tops_1 @ sk_A @ 
% 1.71/1.95              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 1.71/1.95             (k1_tops_1 @ sk_A @ X0))
% 1.71/1.95          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.71/1.95               X0))),
% 1.71/1.95      inference('sup-', [status(thm)], ['122', '123'])).
% 1.71/1.95  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('126', plain,
% 1.71/1.95      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.71/1.95        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('demod', [status(thm)], ['4', '5'])).
% 1.71/1.95  thf('127', plain,
% 1.71/1.95      (![X20 : $i, X21 : $i]:
% 1.71/1.95         (~ (l1_pre_topc @ X20)
% 1.71/1.95          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.71/1.95          | ((k1_tops_1 @ X20 @ (k1_tops_1 @ X20 @ X21))
% 1.71/1.95              = (k1_tops_1 @ X20 @ X21)))),
% 1.71/1.95      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 1.71/1.95  thf('128', plain,
% 1.71/1.95      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 1.71/1.95          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 1.71/1.95        | ~ (l1_pre_topc @ sk_A))),
% 1.71/1.95      inference('sup-', [status(thm)], ['126', '127'])).
% 1.71/1.95  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('130', plain,
% 1.71/1.95      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 1.71/1.95         = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.71/1.95      inference('demod', [status(thm)], ['128', '129'])).
% 1.71/1.95  thf('131', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.71/1.95          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.71/1.95             (k1_tops_1 @ sk_A @ X0))
% 1.71/1.95          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.71/1.95               X0))),
% 1.71/1.95      inference('demod', [status(thm)], ['124', '125', '130'])).
% 1.71/1.95  thf('132', plain,
% 1.71/1.95      (((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.71/1.95         (k1_tops_1 @ sk_A @ sk_B))
% 1.71/1.95        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.71/1.95      inference('sup-', [status(thm)], ['121', '131'])).
% 1.71/1.95  thf('133', plain,
% 1.71/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('134', plain,
% 1.71/1.95      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.71/1.95        (k1_tops_1 @ sk_A @ sk_B))),
% 1.71/1.95      inference('demod', [status(thm)], ['132', '133'])).
% 1.71/1.95  thf('135', plain, ((v4_tops_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.71/1.95      inference('demod', [status(thm)], ['120', '134'])).
% 1.71/1.95  thf('136', plain, ($false), inference('demod', [status(thm)], ['102', '135'])).
% 1.71/1.95  
% 1.71/1.95  % SZS output end Refutation
% 1.71/1.95  
% 1.71/1.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
