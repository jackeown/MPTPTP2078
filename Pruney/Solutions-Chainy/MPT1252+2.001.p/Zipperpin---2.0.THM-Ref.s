%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4M7sEIpTGR

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:12 EST 2020

% Result     : Theorem 7.59s
% Output     : Refutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 442 expanded)
%              Number of leaves         :   26 ( 137 expanded)
%              Depth                    :   15
%              Number of atoms          : 1733 (5456 expanded)
%              Number of equality atoms :   42 (  67 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t68_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t68_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t41_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X14 @ ( k4_subset_1 @ X14 @ X15 @ X13 ) ) @ ( k3_subset_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('15',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) )
      | ( ( k4_subset_1 @ X4 @ X3 @ X5 )
        = ( k4_subset_1 @ X4 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k2_pre_topc @ X30 @ X29 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ ( k2_tops_1 @ X30 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('28',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ( r1_tarski @ ( k3_subset_1 @ X11 @ X10 ) @ ( k3_subset_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X9 @ ( k3_subset_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('33',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X9 @ ( k3_subset_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('42',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('45',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','42','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('48',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('49',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X14 @ ( k4_subset_1 @ X14 @ X15 @ X13 ) ) @ ( k3_subset_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('53',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('56',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ( r1_tarski @ ( k3_subset_1 @ X11 @ X10 ) @ ( k3_subset_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('60',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X9 @ ( k3_subset_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('61',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','62'])).

thf('64',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('65',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('66',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('71',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('76',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('78',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf(t51_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ X21 @ ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ X22 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ X20 ) @ ( k2_pre_topc @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t51_pre_topc])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('85',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_pre_topc @ X18 @ ( k2_pre_topc @ X18 @ X19 ) )
        = ( k2_pre_topc @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('86',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['82','83','88'])).

thf('90',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','89'])).

thf('91',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('92',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k2_tops_1 @ X24 @ X23 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k2_pre_topc @ X24 @ X23 ) @ ( k2_pre_topc @ X24 @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X9 @ ( k3_subset_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('97',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94','97'])).

thf('99',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('100',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k2_tops_1 @ X28 @ X27 )
        = ( k2_tops_1 @ X28 @ ( k3_subset_1 @ ( u1_struct_0 @ X28 ) @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['95','96'])).

thf('104',plain,
    ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_pre_topc @ X18 @ ( k2_pre_topc @ X18 @ X19 ) )
        = ( k2_pre_topc @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('108',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','104'])).

thf('112',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['90','105','110','111'])).

thf('113',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['68','112'])).

thf('114',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['0','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4M7sEIpTGR
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.59/7.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.59/7.82  % Solved by: fo/fo7.sh
% 7.59/7.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.59/7.82  % done 2152 iterations in 7.364s
% 7.59/7.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.59/7.82  % SZS output start Refutation
% 7.59/7.82  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 7.59/7.82  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.59/7.82  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 7.59/7.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.59/7.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.59/7.82  thf(sk_B_type, type, sk_B: $i).
% 7.59/7.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.59/7.82  thf(sk_A_type, type, sk_A: $i).
% 7.59/7.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.59/7.82  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 7.59/7.82  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 7.59/7.82  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 7.59/7.82  thf(t68_tops_1, conjecture,
% 7.59/7.82    (![A:$i]:
% 7.59/7.82     ( ( l1_pre_topc @ A ) =>
% 7.59/7.82       ( ![B:$i]:
% 7.59/7.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.59/7.82           ( r1_tarski @
% 7.59/7.82             ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 7.59/7.82  thf(zf_stmt_0, negated_conjecture,
% 7.59/7.82    (~( ![A:$i]:
% 7.59/7.82        ( ( l1_pre_topc @ A ) =>
% 7.59/7.82          ( ![B:$i]:
% 7.59/7.82            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.59/7.82              ( r1_tarski @
% 7.59/7.82                ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) @ 
% 7.59/7.82                ( k2_tops_1 @ A @ B ) ) ) ) ) )),
% 7.59/7.82    inference('cnf.neg', [status(esa)], [t68_tops_1])).
% 7.59/7.82  thf('0', plain,
% 7.59/7.82      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82          (k2_tops_1 @ sk_A @ sk_B))),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('1', plain,
% 7.59/7.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf(dt_k2_tops_1, axiom,
% 7.59/7.82    (![A:$i,B:$i]:
% 7.59/7.82     ( ( ( l1_pre_topc @ A ) & 
% 7.59/7.82         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.59/7.82       ( m1_subset_1 @
% 7.59/7.82         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.59/7.82  thf('2', plain,
% 7.59/7.82      (![X25 : $i, X26 : $i]:
% 7.59/7.82         (~ (l1_pre_topc @ X25)
% 7.59/7.82          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 7.59/7.82          | (m1_subset_1 @ (k2_tops_1 @ X25 @ X26) @ 
% 7.59/7.82             (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 7.59/7.82      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 7.59/7.82  thf('3', plain,
% 7.59/7.82      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.59/7.82        | ~ (l1_pre_topc @ sk_A))),
% 7.59/7.82      inference('sup-', [status(thm)], ['1', '2'])).
% 7.59/7.82  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('5', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['3', '4'])).
% 7.59/7.82  thf('6', plain,
% 7.59/7.82      (![X25 : $i, X26 : $i]:
% 7.59/7.82         (~ (l1_pre_topc @ X25)
% 7.59/7.82          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 7.59/7.82          | (m1_subset_1 @ (k2_tops_1 @ X25 @ X26) @ 
% 7.59/7.82             (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 7.59/7.82      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 7.59/7.82  thf('7', plain,
% 7.59/7.82      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.59/7.82        | ~ (l1_pre_topc @ sk_A))),
% 7.59/7.82      inference('sup-', [status(thm)], ['5', '6'])).
% 7.59/7.82  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('9', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['7', '8'])).
% 7.59/7.82  thf('10', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['3', '4'])).
% 7.59/7.82  thf(t41_subset_1, axiom,
% 7.59/7.82    (![A:$i,B:$i]:
% 7.59/7.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.59/7.82       ( ![C:$i]:
% 7.59/7.82         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.59/7.82           ( r1_tarski @
% 7.59/7.82             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 7.59/7.82             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 7.59/7.82  thf('11', plain,
% 7.59/7.82      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 7.59/7.82          | (r1_tarski @ 
% 7.59/7.82             (k3_subset_1 @ X14 @ (k4_subset_1 @ X14 @ X15 @ X13)) @ 
% 7.59/7.82             (k3_subset_1 @ X14 @ X15))
% 7.59/7.82          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 7.59/7.82      inference('cnf', [status(esa)], [t41_subset_1])).
% 7.59/7.82  thf('12', plain,
% 7.59/7.82      (![X0 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.59/7.82          | (r1_tarski @ 
% 7.59/7.82             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 7.59/7.82               (k2_tops_1 @ sk_A @ sk_B))) @ 
% 7.59/7.82             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['10', '11'])).
% 7.59/7.82  thf('13', plain,
% 7.59/7.82      ((r1_tarski @ 
% 7.59/7.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82          (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82          (k2_tops_1 @ sk_A @ sk_B))) @ 
% 7.59/7.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 7.59/7.82      inference('sup-', [status(thm)], ['9', '12'])).
% 7.59/7.82  thf('14', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['3', '4'])).
% 7.59/7.82  thf('15', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['7', '8'])).
% 7.59/7.82  thf(commutativity_k4_subset_1, axiom,
% 7.59/7.82    (![A:$i,B:$i,C:$i]:
% 7.59/7.82     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 7.59/7.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 7.59/7.82       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 7.59/7.82  thf('16', plain,
% 7.59/7.82      (![X3 : $i, X4 : $i, X5 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 7.59/7.82          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4))
% 7.59/7.82          | ((k4_subset_1 @ X4 @ X3 @ X5) = (k4_subset_1 @ X4 @ X5 @ X3)))),
% 7.59/7.82      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 7.59/7.82  thf('17', plain,
% 7.59/7.82      (![X0 : $i]:
% 7.59/7.82         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82            (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 7.59/7.82            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 7.59/7.82               (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))
% 7.59/7.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.59/7.82      inference('sup-', [status(thm)], ['15', '16'])).
% 7.59/7.82  thf('18', plain,
% 7.59/7.82      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82         (k2_tops_1 @ sk_A @ sk_B))
% 7.59/7.82         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82            (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 7.59/7.82      inference('sup-', [status(thm)], ['14', '17'])).
% 7.59/7.82  thf('19', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['3', '4'])).
% 7.59/7.82  thf(t65_tops_1, axiom,
% 7.59/7.82    (![A:$i]:
% 7.59/7.82     ( ( l1_pre_topc @ A ) =>
% 7.59/7.82       ( ![B:$i]:
% 7.59/7.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.59/7.82           ( ( k2_pre_topc @ A @ B ) =
% 7.59/7.82             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 7.59/7.82  thf('20', plain,
% 7.59/7.82      (![X29 : $i, X30 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 7.59/7.82          | ((k2_pre_topc @ X30 @ X29)
% 7.59/7.82              = (k4_subset_1 @ (u1_struct_0 @ X30) @ X29 @ 
% 7.59/7.82                 (k2_tops_1 @ X30 @ X29)))
% 7.59/7.82          | ~ (l1_pre_topc @ X30))),
% 7.59/7.82      inference('cnf', [status(esa)], [t65_tops_1])).
% 7.59/7.82  thf('21', plain,
% 7.59/7.82      ((~ (l1_pre_topc @ sk_A)
% 7.59/7.82        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 7.59/7.82            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82               (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82               (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 7.59/7.82      inference('sup-', [status(thm)], ['19', '20'])).
% 7.59/7.82  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('23', plain,
% 7.59/7.82      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 7.59/7.82         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82            (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 7.59/7.82      inference('demod', [status(thm)], ['21', '22'])).
% 7.59/7.82  thf('24', plain,
% 7.59/7.82      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82         (k2_tops_1 @ sk_A @ sk_B))
% 7.59/7.82         = (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.59/7.82      inference('demod', [status(thm)], ['18', '23'])).
% 7.59/7.82  thf('25', plain,
% 7.59/7.82      ((r1_tarski @ 
% 7.59/7.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 7.59/7.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 7.59/7.82      inference('demod', [status(thm)], ['13', '24'])).
% 7.59/7.82  thf('26', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['7', '8'])).
% 7.59/7.82  thf(dt_k3_subset_1, axiom,
% 7.59/7.82    (![A:$i,B:$i]:
% 7.59/7.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.59/7.82       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 7.59/7.82  thf('27', plain,
% 7.59/7.82      (![X6 : $i, X7 : $i]:
% 7.59/7.82         ((m1_subset_1 @ (k3_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 7.59/7.82          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 7.59/7.82      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.59/7.82  thf('28', plain,
% 7.59/7.82      ((m1_subset_1 @ 
% 7.59/7.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['26', '27'])).
% 7.59/7.82  thf(t31_subset_1, axiom,
% 7.59/7.82    (![A:$i,B:$i]:
% 7.59/7.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.59/7.82       ( ![C:$i]:
% 7.59/7.82         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.59/7.82           ( ( r1_tarski @ B @ C ) <=>
% 7.59/7.82             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 7.59/7.82  thf('29', plain,
% 7.59/7.82      (![X10 : $i, X11 : $i, X12 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 7.59/7.82          | ~ (r1_tarski @ X12 @ X10)
% 7.59/7.82          | (r1_tarski @ (k3_subset_1 @ X11 @ X10) @ (k3_subset_1 @ X11 @ X12))
% 7.59/7.82          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 7.59/7.82      inference('cnf', [status(esa)], [t31_subset_1])).
% 7.59/7.82  thf('30', plain,
% 7.59/7.82      (![X0 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.59/7.82          | (r1_tarski @ 
% 7.59/7.82             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82               (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))) @ 
% 7.59/7.82             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 7.59/7.82          | ~ (r1_tarski @ X0 @ 
% 7.59/7.82               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 7.59/7.82      inference('sup-', [status(thm)], ['28', '29'])).
% 7.59/7.82  thf('31', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['7', '8'])).
% 7.59/7.82  thf(involutiveness_k3_subset_1, axiom,
% 7.59/7.82    (![A:$i,B:$i]:
% 7.59/7.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.59/7.82       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 7.59/7.82  thf('32', plain,
% 7.59/7.82      (![X8 : $i, X9 : $i]:
% 7.59/7.82         (((k3_subset_1 @ X9 @ (k3_subset_1 @ X9 @ X8)) = (X8))
% 7.59/7.82          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 7.59/7.82      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.59/7.82  thf('33', plain,
% 7.59/7.82      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82          (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))
% 7.59/7.82         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['31', '32'])).
% 7.59/7.82  thf('34', plain,
% 7.59/7.82      (![X0 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.59/7.82          | (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 7.59/7.82          | ~ (r1_tarski @ X0 @ 
% 7.59/7.82               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 7.59/7.82      inference('demod', [status(thm)], ['30', '33'])).
% 7.59/7.82  thf('35', plain,
% 7.59/7.82      (((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82           (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))
% 7.59/7.82        | ~ (m1_subset_1 @ 
% 7.59/7.82             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82              (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 7.59/7.82             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.59/7.82      inference('sup-', [status(thm)], ['25', '34'])).
% 7.59/7.82  thf('36', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['3', '4'])).
% 7.59/7.82  thf(dt_k2_pre_topc, axiom,
% 7.59/7.82    (![A:$i,B:$i]:
% 7.59/7.82     ( ( ( l1_pre_topc @ A ) & 
% 7.59/7.82         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.59/7.82       ( m1_subset_1 @
% 7.59/7.82         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.59/7.82  thf('37', plain,
% 7.59/7.82      (![X16 : $i, X17 : $i]:
% 7.59/7.82         (~ (l1_pre_topc @ X16)
% 7.59/7.82          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 7.59/7.82          | (m1_subset_1 @ (k2_pre_topc @ X16 @ X17) @ 
% 7.59/7.82             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 7.59/7.82      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 7.59/7.82  thf('38', plain,
% 7.59/7.82      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.59/7.82        | ~ (l1_pre_topc @ sk_A))),
% 7.59/7.82      inference('sup-', [status(thm)], ['36', '37'])).
% 7.59/7.82  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('40', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['38', '39'])).
% 7.59/7.82  thf('41', plain,
% 7.59/7.82      (![X8 : $i, X9 : $i]:
% 7.59/7.82         (((k3_subset_1 @ X9 @ (k3_subset_1 @ X9 @ X8)) = (X8))
% 7.59/7.82          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 7.59/7.82      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.59/7.82  thf('42', plain,
% 7.59/7.82      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82          (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))
% 7.59/7.82         = (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['40', '41'])).
% 7.59/7.82  thf('43', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['38', '39'])).
% 7.59/7.82  thf('44', plain,
% 7.59/7.82      (![X6 : $i, X7 : $i]:
% 7.59/7.82         ((m1_subset_1 @ (k3_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 7.59/7.82          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 7.59/7.82      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.59/7.82  thf('45', plain,
% 7.59/7.82      ((m1_subset_1 @ 
% 7.59/7.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['43', '44'])).
% 7.59/7.82  thf('46', plain,
% 7.59/7.82      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82        (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.59/7.82      inference('demod', [status(thm)], ['35', '42', '45'])).
% 7.59/7.82  thf('47', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['3', '4'])).
% 7.59/7.82  thf('48', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['7', '8'])).
% 7.59/7.82  thf('49', plain,
% 7.59/7.82      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 7.59/7.82          | (r1_tarski @ 
% 7.59/7.82             (k3_subset_1 @ X14 @ (k4_subset_1 @ X14 @ X15 @ X13)) @ 
% 7.59/7.82             (k3_subset_1 @ X14 @ X15))
% 7.59/7.82          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 7.59/7.82      inference('cnf', [status(esa)], [t41_subset_1])).
% 7.59/7.82  thf('50', plain,
% 7.59/7.82      (![X0 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.59/7.82          | (r1_tarski @ 
% 7.59/7.82             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 7.59/7.82               (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))) @ 
% 7.59/7.82             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['48', '49'])).
% 7.59/7.82  thf('51', plain,
% 7.59/7.82      ((r1_tarski @ 
% 7.59/7.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82          (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))) @ 
% 7.59/7.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['47', '50'])).
% 7.59/7.82  thf('52', plain,
% 7.59/7.82      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 7.59/7.82         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82            (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 7.59/7.82      inference('demod', [status(thm)], ['21', '22'])).
% 7.59/7.82  thf('53', plain,
% 7.59/7.82      ((r1_tarski @ 
% 7.59/7.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 7.59/7.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.59/7.82      inference('demod', [status(thm)], ['51', '52'])).
% 7.59/7.82  thf('54', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['3', '4'])).
% 7.59/7.82  thf('55', plain,
% 7.59/7.82      (![X6 : $i, X7 : $i]:
% 7.59/7.82         ((m1_subset_1 @ (k3_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 7.59/7.82          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 7.59/7.82      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.59/7.82  thf('56', plain,
% 7.59/7.82      ((m1_subset_1 @ 
% 7.59/7.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['54', '55'])).
% 7.59/7.82  thf('57', plain,
% 7.59/7.82      (![X10 : $i, X11 : $i, X12 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 7.59/7.82          | ~ (r1_tarski @ X12 @ X10)
% 7.59/7.82          | (r1_tarski @ (k3_subset_1 @ X11 @ X10) @ (k3_subset_1 @ X11 @ X12))
% 7.59/7.82          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 7.59/7.82      inference('cnf', [status(esa)], [t31_subset_1])).
% 7.59/7.82  thf('58', plain,
% 7.59/7.82      (![X0 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.59/7.82          | (r1_tarski @ 
% 7.59/7.82             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 7.59/7.82             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 7.59/7.82          | ~ (r1_tarski @ X0 @ 
% 7.59/7.82               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 7.59/7.82      inference('sup-', [status(thm)], ['56', '57'])).
% 7.59/7.82  thf('59', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['3', '4'])).
% 7.59/7.82  thf('60', plain,
% 7.59/7.82      (![X8 : $i, X9 : $i]:
% 7.59/7.82         (((k3_subset_1 @ X9 @ (k3_subset_1 @ X9 @ X8)) = (X8))
% 7.59/7.82          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 7.59/7.82      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.59/7.82  thf('61', plain,
% 7.59/7.82      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 7.59/7.82         = (k2_tops_1 @ sk_A @ sk_B))),
% 7.59/7.82      inference('sup-', [status(thm)], ['59', '60'])).
% 7.59/7.82  thf('62', plain,
% 7.59/7.82      (![X0 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.59/7.82          | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 7.59/7.82          | ~ (r1_tarski @ X0 @ 
% 7.59/7.82               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 7.59/7.82      inference('demod', [status(thm)], ['58', '61'])).
% 7.59/7.82  thf('63', plain,
% 7.59/7.82      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82           (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))
% 7.59/7.82        | ~ (m1_subset_1 @ 
% 7.59/7.82             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82              (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 7.59/7.82             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.59/7.82      inference('sup-', [status(thm)], ['53', '62'])).
% 7.59/7.82  thf('64', plain,
% 7.59/7.82      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82          (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))
% 7.59/7.82         = (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['40', '41'])).
% 7.59/7.82  thf('65', plain,
% 7.59/7.82      ((m1_subset_1 @ 
% 7.59/7.82        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['43', '44'])).
% 7.59/7.82  thf('66', plain,
% 7.59/7.82      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.59/7.82        (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.59/7.82      inference('demod', [status(thm)], ['63', '64', '65'])).
% 7.59/7.82  thf(d10_xboole_0, axiom,
% 7.59/7.82    (![A:$i,B:$i]:
% 7.59/7.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.59/7.82  thf('67', plain,
% 7.59/7.82      (![X0 : $i, X2 : $i]:
% 7.59/7.82         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 7.59/7.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.59/7.82  thf('68', plain,
% 7.59/7.82      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82           (k2_tops_1 @ sk_A @ sk_B))
% 7.59/7.82        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 7.59/7.82            = (k2_tops_1 @ sk_A @ sk_B)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['66', '67'])).
% 7.59/7.82  thf('69', plain,
% 7.59/7.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('70', plain,
% 7.59/7.82      (![X16 : $i, X17 : $i]:
% 7.59/7.82         (~ (l1_pre_topc @ X16)
% 7.59/7.82          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 7.59/7.82          | (m1_subset_1 @ (k2_pre_topc @ X16 @ X17) @ 
% 7.59/7.82             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 7.59/7.82      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 7.59/7.82  thf('71', plain,
% 7.59/7.82      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.59/7.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.59/7.82        | ~ (l1_pre_topc @ sk_A))),
% 7.59/7.82      inference('sup-', [status(thm)], ['69', '70'])).
% 7.59/7.82  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('73', plain,
% 7.59/7.82      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['71', '72'])).
% 7.59/7.82  thf('74', plain,
% 7.59/7.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('75', plain,
% 7.59/7.82      (![X6 : $i, X7 : $i]:
% 7.59/7.82         ((m1_subset_1 @ (k3_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 7.59/7.82          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 7.59/7.82      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.59/7.82  thf('76', plain,
% 7.59/7.82      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['74', '75'])).
% 7.59/7.82  thf('77', plain,
% 7.59/7.82      (![X16 : $i, X17 : $i]:
% 7.59/7.82         (~ (l1_pre_topc @ X16)
% 7.59/7.82          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 7.59/7.82          | (m1_subset_1 @ (k2_pre_topc @ X16 @ X17) @ 
% 7.59/7.82             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 7.59/7.82      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 7.59/7.82  thf('78', plain,
% 7.59/7.82      (((m1_subset_1 @ 
% 7.59/7.82         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.59/7.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.59/7.82        | ~ (l1_pre_topc @ sk_A))),
% 7.59/7.82      inference('sup-', [status(thm)], ['76', '77'])).
% 7.59/7.82  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('80', plain,
% 7.59/7.82      ((m1_subset_1 @ 
% 7.59/7.82        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('demod', [status(thm)], ['78', '79'])).
% 7.59/7.82  thf(t51_pre_topc, axiom,
% 7.59/7.82    (![A:$i]:
% 7.59/7.82     ( ( l1_pre_topc @ A ) =>
% 7.59/7.82       ( ![B:$i]:
% 7.59/7.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.59/7.82           ( ![C:$i]:
% 7.59/7.82             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.59/7.82               ( r1_tarski @
% 7.59/7.82                 ( k2_pre_topc @
% 7.59/7.82                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 7.59/7.82                 ( k9_subset_1 @
% 7.59/7.82                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 7.59/7.82                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 7.59/7.82  thf('81', plain,
% 7.59/7.82      (![X20 : $i, X21 : $i, X22 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 7.59/7.82          | (r1_tarski @ 
% 7.59/7.82             (k2_pre_topc @ X21 @ 
% 7.59/7.82              (k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X22)) @ 
% 7.59/7.82             (k9_subset_1 @ (u1_struct_0 @ X21) @ (k2_pre_topc @ X21 @ X20) @ 
% 7.59/7.82              (k2_pre_topc @ X21 @ X22)))
% 7.59/7.82          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 7.59/7.82          | ~ (l1_pre_topc @ X21))),
% 7.59/7.82      inference('cnf', [status(esa)], [t51_pre_topc])).
% 7.59/7.82  thf('82', plain,
% 7.59/7.82      (![X0 : $i]:
% 7.59/7.82         (~ (l1_pre_topc @ sk_A)
% 7.59/7.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.59/7.82          | (r1_tarski @ 
% 7.59/7.82             (k2_pre_topc @ sk_A @ 
% 7.59/7.82              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82               (k2_pre_topc @ sk_A @ 
% 7.59/7.82                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.59/7.82               X0)) @ 
% 7.59/7.82             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82              (k2_pre_topc @ sk_A @ 
% 7.59/7.82               (k2_pre_topc @ sk_A @ 
% 7.59/7.82                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 7.59/7.82              (k2_pre_topc @ sk_A @ X0))))),
% 7.59/7.82      inference('sup-', [status(thm)], ['80', '81'])).
% 7.59/7.82  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('84', plain,
% 7.59/7.82      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['74', '75'])).
% 7.59/7.82  thf(projectivity_k2_pre_topc, axiom,
% 7.59/7.82    (![A:$i,B:$i]:
% 7.59/7.82     ( ( ( l1_pre_topc @ A ) & 
% 7.59/7.82         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.59/7.82       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 7.59/7.82         ( k2_pre_topc @ A @ B ) ) ))).
% 7.59/7.82  thf('85', plain,
% 7.59/7.82      (![X18 : $i, X19 : $i]:
% 7.59/7.82         (~ (l1_pre_topc @ X18)
% 7.59/7.82          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 7.59/7.82          | ((k2_pre_topc @ X18 @ (k2_pre_topc @ X18 @ X19))
% 7.59/7.82              = (k2_pre_topc @ X18 @ X19)))),
% 7.59/7.82      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 7.59/7.82  thf('86', plain,
% 7.59/7.82      ((((k2_pre_topc @ sk_A @ 
% 7.59/7.82          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 7.59/7.82          = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 7.59/7.82        | ~ (l1_pre_topc @ sk_A))),
% 7.59/7.82      inference('sup-', [status(thm)], ['84', '85'])).
% 7.59/7.82  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('88', plain,
% 7.59/7.82      (((k2_pre_topc @ sk_A @ 
% 7.59/7.82         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 7.59/7.82         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 7.59/7.82      inference('demod', [status(thm)], ['86', '87'])).
% 7.59/7.82  thf('89', plain,
% 7.59/7.82      (![X0 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.59/7.82          | (r1_tarski @ 
% 7.59/7.82             (k2_pre_topc @ sk_A @ 
% 7.59/7.82              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82               (k2_pre_topc @ sk_A @ 
% 7.59/7.82                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.59/7.82               X0)) @ 
% 7.59/7.82             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82              (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.59/7.82              (k2_pre_topc @ sk_A @ X0))))),
% 7.59/7.82      inference('demod', [status(thm)], ['82', '83', '88'])).
% 7.59/7.82  thf('90', plain,
% 7.59/7.82      ((r1_tarski @ 
% 7.59/7.82        (k2_pre_topc @ sk_A @ 
% 7.59/7.82         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.59/7.82          (k2_pre_topc @ sk_A @ sk_B))) @ 
% 7.59/7.82        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.59/7.82         (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 7.59/7.82      inference('sup-', [status(thm)], ['73', '89'])).
% 7.59/7.82  thf('91', plain,
% 7.59/7.82      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['74', '75'])).
% 7.59/7.82  thf(d2_tops_1, axiom,
% 7.59/7.82    (![A:$i]:
% 7.59/7.82     ( ( l1_pre_topc @ A ) =>
% 7.59/7.82       ( ![B:$i]:
% 7.59/7.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.59/7.82           ( ( k2_tops_1 @ A @ B ) =
% 7.59/7.82             ( k9_subset_1 @
% 7.59/7.82               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 7.59/7.82               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 7.59/7.82  thf('92', plain,
% 7.59/7.82      (![X23 : $i, X24 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 7.59/7.82          | ((k2_tops_1 @ X24 @ X23)
% 7.59/7.82              = (k9_subset_1 @ (u1_struct_0 @ X24) @ 
% 7.59/7.82                 (k2_pre_topc @ X24 @ X23) @ 
% 7.59/7.82                 (k2_pre_topc @ X24 @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23))))
% 7.59/7.82          | ~ (l1_pre_topc @ X24))),
% 7.59/7.82      inference('cnf', [status(esa)], [d2_tops_1])).
% 7.59/7.82  thf('93', plain,
% 7.59/7.82      ((~ (l1_pre_topc @ sk_A)
% 7.59/7.82        | ((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.59/7.82            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82               (k2_pre_topc @ sk_A @ 
% 7.59/7.82                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.59/7.82               (k2_pre_topc @ sk_A @ 
% 7.59/7.82                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 7.59/7.82      inference('sup-', [status(thm)], ['91', '92'])).
% 7.59/7.82  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('95', plain,
% 7.59/7.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('96', plain,
% 7.59/7.82      (![X8 : $i, X9 : $i]:
% 7.59/7.82         (((k3_subset_1 @ X9 @ (k3_subset_1 @ X9 @ X8)) = (X8))
% 7.59/7.82          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 7.59/7.82      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.59/7.82  thf('97', plain,
% 7.59/7.82      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 7.59/7.82      inference('sup-', [status(thm)], ['95', '96'])).
% 7.59/7.82  thf('98', plain,
% 7.59/7.82      (((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.59/7.82         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.59/7.82            (k2_pre_topc @ sk_A @ sk_B)))),
% 7.59/7.82      inference('demod', [status(thm)], ['93', '94', '97'])).
% 7.59/7.82  thf('99', plain,
% 7.59/7.82      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.59/7.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('sup-', [status(thm)], ['74', '75'])).
% 7.59/7.82  thf(t62_tops_1, axiom,
% 7.59/7.82    (![A:$i]:
% 7.59/7.82     ( ( l1_pre_topc @ A ) =>
% 7.59/7.82       ( ![B:$i]:
% 7.59/7.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.59/7.82           ( ( k2_tops_1 @ A @ B ) =
% 7.59/7.82             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 7.59/7.82  thf('100', plain,
% 7.59/7.82      (![X27 : $i, X28 : $i]:
% 7.59/7.82         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.59/7.82          | ((k2_tops_1 @ X28 @ X27)
% 7.59/7.82              = (k2_tops_1 @ X28 @ (k3_subset_1 @ (u1_struct_0 @ X28) @ X27)))
% 7.59/7.82          | ~ (l1_pre_topc @ X28))),
% 7.59/7.82      inference('cnf', [status(esa)], [t62_tops_1])).
% 7.59/7.82  thf('101', plain,
% 7.59/7.82      ((~ (l1_pre_topc @ sk_A)
% 7.59/7.82        | ((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.59/7.82            = (k2_tops_1 @ sk_A @ 
% 7.59/7.82               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 7.59/7.82      inference('sup-', [status(thm)], ['99', '100'])).
% 7.59/7.82  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('103', plain,
% 7.59/7.82      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 7.59/7.82      inference('sup-', [status(thm)], ['95', '96'])).
% 7.59/7.82  thf('104', plain,
% 7.59/7.82      (((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.59/7.82         = (k2_tops_1 @ sk_A @ sk_B))),
% 7.59/7.82      inference('demod', [status(thm)], ['101', '102', '103'])).
% 7.59/7.82  thf('105', plain,
% 7.59/7.82      (((k2_tops_1 @ sk_A @ sk_B)
% 7.59/7.82         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.59/7.82            (k2_pre_topc @ sk_A @ sk_B)))),
% 7.59/7.82      inference('demod', [status(thm)], ['98', '104'])).
% 7.59/7.82  thf('106', plain,
% 7.59/7.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('107', plain,
% 7.59/7.82      (![X18 : $i, X19 : $i]:
% 7.59/7.82         (~ (l1_pre_topc @ X18)
% 7.59/7.82          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 7.59/7.82          | ((k2_pre_topc @ X18 @ (k2_pre_topc @ X18 @ X19))
% 7.59/7.82              = (k2_pre_topc @ X18 @ X19)))),
% 7.59/7.82      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 7.59/7.82  thf('108', plain,
% 7.59/7.82      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.59/7.82          = (k2_pre_topc @ sk_A @ sk_B))
% 7.59/7.82        | ~ (l1_pre_topc @ sk_A))),
% 7.59/7.82      inference('sup-', [status(thm)], ['106', '107'])).
% 7.59/7.82  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 7.59/7.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.82  thf('110', plain,
% 7.59/7.82      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.59/7.82         = (k2_pre_topc @ sk_A @ sk_B))),
% 7.59/7.82      inference('demod', [status(thm)], ['108', '109'])).
% 7.59/7.82  thf('111', plain,
% 7.59/7.82      (((k2_tops_1 @ sk_A @ sk_B)
% 7.59/7.82         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.59/7.82            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.59/7.82            (k2_pre_topc @ sk_A @ sk_B)))),
% 7.59/7.82      inference('demod', [status(thm)], ['98', '104'])).
% 7.59/7.82  thf('112', plain,
% 7.59/7.82      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82        (k2_tops_1 @ sk_A @ sk_B))),
% 7.59/7.82      inference('demod', [status(thm)], ['90', '105', '110', '111'])).
% 7.59/7.82  thf('113', plain,
% 7.59/7.82      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 7.59/7.82         = (k2_tops_1 @ sk_A @ sk_B))),
% 7.59/7.82      inference('demod', [status(thm)], ['68', '112'])).
% 7.59/7.82  thf('114', plain,
% 7.59/7.82      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.59/7.82        (k2_tops_1 @ sk_A @ sk_B))),
% 7.59/7.82      inference('demod', [status(thm)], ['46', '113'])).
% 7.59/7.82  thf('115', plain, ($false), inference('demod', [status(thm)], ['0', '114'])).
% 7.59/7.82  
% 7.59/7.82  % SZS output end Refutation
% 7.59/7.82  
% 7.59/7.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
