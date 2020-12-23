%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X9fusKOlas

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:12 EST 2020

% Result     : Theorem 41.86s
% Output     : Refutation 41.95s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 273 expanded)
%              Number of leaves         :   24 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          : 1315 (3386 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
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

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('12',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t42_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X12 @ X13 ) @ ( k3_subset_1 @ X12 @ ( k9_subset_1 @ X12 @ X13 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t42_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_tops_1 @ X22 @ X21 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k2_pre_topc @ X22 @ X21 ) @ ( k2_pre_topc @ X22 @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X6 @ X5 ) @ ( k3_subset_1 @ X6 @ X7 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('34',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('36',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t41_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X9 @ ( k4_subset_1 @ X9 @ X10 @ X8 ) ) @ ( k3_subset_1 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('41',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 @ ( k2_tops_1 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X6 @ X5 ) @ ( k3_subset_1 @ X6 @ X7 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('47',plain,
    ( ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('49',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('50',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('55',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(t51_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ X19 @ ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ X20 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k2_pre_topc @ X19 @ X18 ) @ ( k2_pre_topc @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t51_pre_topc])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_pre_topc @ X16 @ ( k2_pre_topc @ X16 @ X17 ) )
        = ( k2_pre_topc @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('70',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['66','67','72'])).

thf('74',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['59','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_tops_1 @ X22 @ X21 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k2_pre_topc @ X22 @ X21 ) @ ( k2_pre_topc @ X22 @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('81',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_pre_topc @ X16 @ ( k2_pre_topc @ X16 @ X17 ) )
        = ( k2_pre_topc @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('82',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('86',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['74','79','84','85'])).

thf('87',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','86'])).

thf('88',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['0','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.X9fusKOlas
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:04:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 41.86/42.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 41.86/42.11  % Solved by: fo/fo7.sh
% 41.86/42.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 41.86/42.11  % done 4148 iterations in 41.657s
% 41.86/42.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 41.86/42.11  % SZS output start Refutation
% 41.86/42.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 41.86/42.11  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 41.86/42.11  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 41.86/42.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 41.86/42.11  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 41.86/42.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 41.86/42.11  thf(sk_A_type, type, sk_A: $i).
% 41.86/42.11  thf(sk_B_type, type, sk_B: $i).
% 41.86/42.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 41.86/42.11  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 41.86/42.11  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 41.86/42.11  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 41.86/42.11  thf(t68_tops_1, conjecture,
% 41.86/42.11    (![A:$i]:
% 41.86/42.11     ( ( l1_pre_topc @ A ) =>
% 41.86/42.11       ( ![B:$i]:
% 41.86/42.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.86/42.11           ( r1_tarski @
% 41.86/42.11             ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 41.86/42.11  thf(zf_stmt_0, negated_conjecture,
% 41.86/42.11    (~( ![A:$i]:
% 41.86/42.11        ( ( l1_pre_topc @ A ) =>
% 41.86/42.11          ( ![B:$i]:
% 41.86/42.11            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.86/42.11              ( r1_tarski @
% 41.86/42.11                ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) @ 
% 41.86/42.11                ( k2_tops_1 @ A @ B ) ) ) ) ) )),
% 41.86/42.11    inference('cnf.neg', [status(esa)], [t68_tops_1])).
% 41.86/42.11  thf('0', plain,
% 41.86/42.11      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.11          (k2_tops_1 @ sk_A @ sk_B))),
% 41.86/42.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.86/42.11  thf('1', plain,
% 41.86/42.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.86/42.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.86/42.11  thf(dt_k2_tops_1, axiom,
% 41.86/42.11    (![A:$i,B:$i]:
% 41.86/42.11     ( ( ( l1_pre_topc @ A ) & 
% 41.86/42.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 41.86/42.11       ( m1_subset_1 @
% 41.86/42.11         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 41.86/42.11  thf('2', plain,
% 41.86/42.11      (![X23 : $i, X24 : $i]:
% 41.86/42.11         (~ (l1_pre_topc @ X23)
% 41.86/42.11          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 41.86/42.11          | (m1_subset_1 @ (k2_tops_1 @ X23 @ X24) @ 
% 41.86/42.11             (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 41.86/42.11      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 41.86/42.11  thf('3', plain,
% 41.86/42.11      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 41.86/42.11         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.86/42.11        | ~ (l1_pre_topc @ sk_A))),
% 41.86/42.11      inference('sup-', [status(thm)], ['1', '2'])).
% 41.86/42.11  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 41.86/42.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.86/42.11  thf('5', plain,
% 41.86/42.11      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 41.86/42.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.86/42.11      inference('demod', [status(thm)], ['3', '4'])).
% 41.86/42.11  thf(dt_k2_pre_topc, axiom,
% 41.86/42.11    (![A:$i,B:$i]:
% 41.86/42.11     ( ( ( l1_pre_topc @ A ) & 
% 41.86/42.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 41.86/42.11       ( m1_subset_1 @
% 41.86/42.11         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 41.86/42.11  thf('6', plain,
% 41.86/42.11      (![X14 : $i, X15 : $i]:
% 41.86/42.11         (~ (l1_pre_topc @ X14)
% 41.86/42.11          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 41.86/42.11          | (m1_subset_1 @ (k2_pre_topc @ X14 @ X15) @ 
% 41.86/42.11             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 41.86/42.11      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 41.86/42.11  thf('7', plain,
% 41.86/42.11      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.11         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.86/42.11        | ~ (l1_pre_topc @ sk_A))),
% 41.86/42.11      inference('sup-', [status(thm)], ['5', '6'])).
% 41.86/42.11  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 41.86/42.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.86/42.11  thf('9', plain,
% 41.86/42.11      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.86/42.11      inference('demod', [status(thm)], ['7', '8'])).
% 41.86/42.11  thf('10', plain,
% 41.86/42.11      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 41.86/42.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.86/42.11      inference('demod', [status(thm)], ['3', '4'])).
% 41.86/42.11  thf(dt_k3_subset_1, axiom,
% 41.86/42.11    (![A:$i,B:$i]:
% 41.86/42.11     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 41.86/42.11       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 41.86/42.11  thf('11', plain,
% 41.86/42.11      (![X3 : $i, X4 : $i]:
% 41.86/42.11         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 41.86/42.11          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 41.86/42.11      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 41.86/42.11  thf('12', plain,
% 41.86/42.11      ((m1_subset_1 @ 
% 41.86/42.11        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.86/42.11      inference('sup-', [status(thm)], ['10', '11'])).
% 41.86/42.11  thf('13', plain,
% 41.86/42.11      (![X14 : $i, X15 : $i]:
% 41.86/42.11         (~ (l1_pre_topc @ X14)
% 41.86/42.11          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 41.86/42.11          | (m1_subset_1 @ (k2_pre_topc @ X14 @ X15) @ 
% 41.86/42.11             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 41.86/42.11      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 41.86/42.11  thf('14', plain,
% 41.86/42.11      (((m1_subset_1 @ 
% 41.86/42.11         (k2_pre_topc @ sk_A @ 
% 41.86/42.11          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 41.86/42.11         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.86/42.12        | ~ (l1_pre_topc @ sk_A))),
% 41.86/42.12      inference('sup-', [status(thm)], ['12', '13'])).
% 41.86/42.12  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 41.86/42.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.86/42.12  thf('16', plain,
% 41.86/42.12      ((m1_subset_1 @ 
% 41.86/42.12        (k2_pre_topc @ sk_A @ 
% 41.86/42.12         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 41.86/42.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.86/42.12      inference('demod', [status(thm)], ['14', '15'])).
% 41.86/42.12  thf(t42_subset_1, axiom,
% 41.86/42.12    (![A:$i,B:$i]:
% 41.86/42.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 41.86/42.12       ( ![C:$i]:
% 41.86/42.12         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 41.86/42.12           ( r1_tarski @
% 41.86/42.12             ( k3_subset_1 @ A @ B ) @ 
% 41.86/42.12             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 41.86/42.12  thf('17', plain,
% 41.86/42.12      (![X11 : $i, X12 : $i, X13 : $i]:
% 41.86/42.12         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 41.86/42.12          | (r1_tarski @ (k3_subset_1 @ X12 @ X13) @ 
% 41.86/42.12             (k3_subset_1 @ X12 @ (k9_subset_1 @ X12 @ X13 @ X11)))
% 41.86/42.12          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 41.86/42.12      inference('cnf', [status(esa)], [t42_subset_1])).
% 41.86/42.12  thf('18', plain,
% 41.86/42.12      (![X0 : $i]:
% 41.86/42.12         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.86/42.12          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 41.86/42.12             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.86/42.12              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 41.86/42.12               (k2_pre_topc @ sk_A @ 
% 41.86/42.12                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))))))),
% 41.86/42.12      inference('sup-', [status(thm)], ['16', '17'])).
% 41.86/42.12  thf('19', plain,
% 41.86/42.12      ((r1_tarski @ 
% 41.86/42.12        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.86/42.12         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 41.86/42.12        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.86/42.12         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.86/42.12          (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.12          (k2_pre_topc @ sk_A @ 
% 41.86/42.12           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 41.86/42.12      inference('sup-', [status(thm)], ['9', '18'])).
% 41.86/42.12  thf('20', plain,
% 41.86/42.12      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 41.86/42.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.86/42.12      inference('demod', [status(thm)], ['3', '4'])).
% 41.86/42.12  thf(d2_tops_1, axiom,
% 41.86/42.12    (![A:$i]:
% 41.86/42.12     ( ( l1_pre_topc @ A ) =>
% 41.86/42.12       ( ![B:$i]:
% 41.86/42.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.86/42.12           ( ( k2_tops_1 @ A @ B ) =
% 41.86/42.12             ( k9_subset_1 @
% 41.86/42.12               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 41.86/42.12               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 41.86/42.12  thf('21', plain,
% 41.86/42.12      (![X21 : $i, X22 : $i]:
% 41.86/42.12         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 41.86/42.12          | ((k2_tops_1 @ X22 @ X21)
% 41.86/42.12              = (k9_subset_1 @ (u1_struct_0 @ X22) @ 
% 41.86/42.12                 (k2_pre_topc @ X22 @ X21) @ 
% 41.86/42.12                 (k2_pre_topc @ X22 @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21))))
% 41.86/42.12          | ~ (l1_pre_topc @ X22))),
% 41.86/42.12      inference('cnf', [status(esa)], [d2_tops_1])).
% 41.86/42.12  thf('22', plain,
% 41.86/42.12      ((~ (l1_pre_topc @ sk_A)
% 41.86/42.12        | ((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 41.86/42.12            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.86/42.12               (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.12               (k2_pre_topc @ sk_A @ 
% 41.86/42.12                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 41.86/42.12      inference('sup-', [status(thm)], ['20', '21'])).
% 41.86/42.12  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 41.86/42.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.86/42.12  thf('24', plain,
% 41.86/42.12      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 41.86/42.12         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.86/42.12            (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.12            (k2_pre_topc @ sk_A @ 
% 41.86/42.12             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 41.86/42.12      inference('demod', [status(thm)], ['22', '23'])).
% 41.86/42.12  thf('25', plain,
% 41.86/42.12      ((r1_tarski @ 
% 41.86/42.12        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.86/42.12         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 41.86/42.12        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.86/42.12         (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 41.86/42.12      inference('demod', [status(thm)], ['19', '24'])).
% 41.86/42.12  thf(t31_subset_1, axiom,
% 41.86/42.12    (![A:$i,B:$i]:
% 41.86/42.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 41.86/42.12       ( ![C:$i]:
% 41.86/42.12         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 41.86/42.12           ( ( r1_tarski @ B @ C ) <=>
% 41.86/42.12             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 41.86/42.12  thf('26', plain,
% 41.86/42.12      (![X5 : $i, X6 : $i, X7 : $i]:
% 41.86/42.12         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 41.86/42.12          | ~ (r1_tarski @ (k3_subset_1 @ X6 @ X5) @ (k3_subset_1 @ X6 @ X7))
% 41.86/42.12          | (r1_tarski @ X7 @ X5)
% 41.86/42.12          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 41.86/42.12      inference('cnf', [status(esa)], [t31_subset_1])).
% 41.86/42.12  thf('27', plain,
% 41.86/42.12      ((~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.12           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.86/42.12        | (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.12           (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 41.86/42.12        | ~ (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.12             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 41.86/42.12      inference('sup-', [status(thm)], ['25', '26'])).
% 41.86/42.12  thf('28', plain,
% 41.86/42.12      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 41.86/42.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.86/42.12      inference('demod', [status(thm)], ['3', '4'])).
% 41.86/42.12  thf('29', plain,
% 41.86/42.12      (![X23 : $i, X24 : $i]:
% 41.86/42.12         (~ (l1_pre_topc @ X23)
% 41.86/42.12          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 41.86/42.12          | (m1_subset_1 @ (k2_tops_1 @ X23 @ X24) @ 
% 41.86/42.12             (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 41.86/42.12      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 41.86/42.12  thf('30', plain,
% 41.86/42.12      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.12         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.86/42.12        | ~ (l1_pre_topc @ sk_A))),
% 41.86/42.12      inference('sup-', [status(thm)], ['28', '29'])).
% 41.86/42.12  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 41.86/42.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.86/42.12  thf('32', plain,
% 41.86/42.12      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.86/42.12      inference('demod', [status(thm)], ['30', '31'])).
% 41.86/42.12  thf('33', plain,
% 41.86/42.12      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.86/42.12      inference('demod', [status(thm)], ['7', '8'])).
% 41.86/42.12  thf('34', plain,
% 41.86/42.12      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.12        (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 41.86/42.12      inference('demod', [status(thm)], ['27', '32', '33'])).
% 41.86/42.12  thf('35', plain,
% 41.86/42.12      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 41.86/42.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.86/42.12      inference('demod', [status(thm)], ['3', '4'])).
% 41.86/42.12  thf('36', plain,
% 41.86/42.12      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.86/42.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.86/42.12      inference('demod', [status(thm)], ['30', '31'])).
% 41.86/42.12  thf(t41_subset_1, axiom,
% 41.86/42.12    (![A:$i,B:$i]:
% 41.86/42.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 41.86/42.12       ( ![C:$i]:
% 41.86/42.12         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 41.86/42.12           ( r1_tarski @
% 41.86/42.12             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 41.86/42.12             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 41.86/42.12  thf('37', plain,
% 41.86/42.12      (![X8 : $i, X9 : $i, X10 : $i]:
% 41.86/42.12         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 41.86/42.12          | (r1_tarski @ (k3_subset_1 @ X9 @ (k4_subset_1 @ X9 @ X10 @ X8)) @ 
% 41.86/42.12             (k3_subset_1 @ X9 @ X10))
% 41.86/42.12          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 41.86/42.12      inference('cnf', [status(esa)], [t41_subset_1])).
% 41.86/42.12  thf('38', plain,
% 41.86/42.12      (![X0 : $i]:
% 41.86/42.12         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.86/42.12          | (r1_tarski @ 
% 41.86/42.12             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.86/42.12              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 41.86/42.12               (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))) @ 
% 41.86/42.12             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 41.86/42.12      inference('sup-', [status(thm)], ['36', '37'])).
% 41.86/42.12  thf('39', plain,
% 41.86/42.12      ((r1_tarski @ 
% 41.86/42.12        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.86/42.12         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 41.86/42.12          (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))) @ 
% 41.86/42.12        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 41.86/42.12      inference('sup-', [status(thm)], ['35', '38'])).
% 41.86/42.12  thf('40', plain,
% 41.86/42.12      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 41.86/42.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.86/42.12      inference('demod', [status(thm)], ['3', '4'])).
% 41.86/42.12  thf(t65_tops_1, axiom,
% 41.86/42.12    (![A:$i]:
% 41.86/42.12     ( ( l1_pre_topc @ A ) =>
% 41.86/42.12       ( ![B:$i]:
% 41.86/42.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.86/42.12           ( ( k2_pre_topc @ A @ B ) =
% 41.86/42.12             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 41.86/42.12  thf('41', plain,
% 41.86/42.12      (![X25 : $i, X26 : $i]:
% 41.86/42.12         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 41.86/42.12          | ((k2_pre_topc @ X26 @ X25)
% 41.86/42.12              = (k4_subset_1 @ (u1_struct_0 @ X26) @ X25 @ 
% 41.86/42.12                 (k2_tops_1 @ X26 @ X25)))
% 41.86/42.12          | ~ (l1_pre_topc @ X26))),
% 41.86/42.12      inference('cnf', [status(esa)], [t65_tops_1])).
% 41.86/42.12  thf('42', plain,
% 41.86/42.12      ((~ (l1_pre_topc @ sk_A)
% 41.86/42.12        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 41.86/42.12            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.86/42.12               (k2_tops_1 @ sk_A @ sk_B) @ 
% 41.86/42.12               (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 41.86/42.12      inference('sup-', [status(thm)], ['40', '41'])).
% 41.86/42.12  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 41.86/42.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.86/42.12  thf('44', plain,
% 41.86/42.12      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 41.86/42.12         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 41.86/42.12            (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 41.86/42.12      inference('demod', [status(thm)], ['42', '43'])).
% 41.86/42.12  thf('45', plain,
% 41.86/42.12      ((r1_tarski @ 
% 41.86/42.12        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.86/42.12         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 41.86/42.12        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 41.86/42.12      inference('demod', [status(thm)], ['39', '44'])).
% 41.86/42.12  thf('46', plain,
% 41.86/42.12      (![X5 : $i, X6 : $i, X7 : $i]:
% 41.86/42.12         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 41.86/42.12          | ~ (r1_tarski @ (k3_subset_1 @ X6 @ X5) @ (k3_subset_1 @ X6 @ X7))
% 41.86/42.12          | (r1_tarski @ X7 @ X5)
% 41.86/42.12          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 41.86/42.12      inference('cnf', [status(esa)], [t31_subset_1])).
% 41.86/42.12  thf('47', plain,
% 41.95/42.12      ((~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 41.95/42.12           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.95/42.12        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 41.95/42.12           (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 41.95/42.12        | ~ (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.95/42.12             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 41.95/42.12      inference('sup-', [status(thm)], ['45', '46'])).
% 41.95/42.12  thf('48', plain,
% 41.95/42.12      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 41.95/42.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.95/42.12      inference('demod', [status(thm)], ['3', '4'])).
% 41.95/42.12  thf('49', plain,
% 41.95/42.12      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.95/42.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.95/42.12      inference('demod', [status(thm)], ['7', '8'])).
% 41.95/42.12  thf('50', plain,
% 41.95/42.12      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 41.95/42.12        (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 41.95/42.12      inference('demod', [status(thm)], ['47', '48', '49'])).
% 41.95/42.12  thf(d10_xboole_0, axiom,
% 41.95/42.12    (![A:$i,B:$i]:
% 41.95/42.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 41.95/42.12  thf('51', plain,
% 41.95/42.12      (![X0 : $i, X2 : $i]:
% 41.95/42.12         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 41.95/42.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 41.95/42.12  thf('52', plain,
% 41.95/42.12      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.95/42.12           (k2_tops_1 @ sk_A @ sk_B))
% 41.95/42.12        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 41.95/42.12            = (k2_tops_1 @ sk_A @ sk_B)))),
% 41.95/42.12      inference('sup-', [status(thm)], ['50', '51'])).
% 41.95/42.12  thf('53', plain,
% 41.95/42.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.95/42.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.95/42.12  thf('54', plain,
% 41.95/42.12      (![X3 : $i, X4 : $i]:
% 41.95/42.12         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 41.95/42.12          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 41.95/42.12      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 41.95/42.12  thf('55', plain,
% 41.95/42.12      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 41.95/42.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.95/42.12      inference('sup-', [status(thm)], ['53', '54'])).
% 41.95/42.12  thf('56', plain,
% 41.95/42.12      (![X14 : $i, X15 : $i]:
% 41.95/42.12         (~ (l1_pre_topc @ X14)
% 41.95/42.12          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 41.95/42.12          | (m1_subset_1 @ (k2_pre_topc @ X14 @ X15) @ 
% 41.95/42.12             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 41.95/42.12      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 41.95/42.12  thf('57', plain,
% 41.95/42.12      (((m1_subset_1 @ 
% 41.95/42.12         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 41.95/42.12         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.95/42.12        | ~ (l1_pre_topc @ sk_A))),
% 41.95/42.12      inference('sup-', [status(thm)], ['55', '56'])).
% 41.95/42.12  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 41.95/42.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.95/42.12  thf('59', plain,
% 41.95/42.12      ((m1_subset_1 @ 
% 41.95/42.12        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 41.95/42.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.95/42.12      inference('demod', [status(thm)], ['57', '58'])).
% 41.95/42.12  thf('60', plain,
% 41.95/42.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.95/42.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.95/42.12  thf('61', plain,
% 41.95/42.12      (![X14 : $i, X15 : $i]:
% 41.95/42.12         (~ (l1_pre_topc @ X14)
% 41.95/42.12          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 41.95/42.12          | (m1_subset_1 @ (k2_pre_topc @ X14 @ X15) @ 
% 41.95/42.12             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 41.95/42.12      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 41.95/42.12  thf('62', plain,
% 41.95/42.12      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 41.95/42.12         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.95/42.12        | ~ (l1_pre_topc @ sk_A))),
% 41.95/42.12      inference('sup-', [status(thm)], ['60', '61'])).
% 41.95/42.12  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 41.95/42.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.95/42.12  thf('64', plain,
% 41.95/42.12      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 41.95/42.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.95/42.12      inference('demod', [status(thm)], ['62', '63'])).
% 41.95/42.12  thf(t51_pre_topc, axiom,
% 41.95/42.12    (![A:$i]:
% 41.95/42.12     ( ( l1_pre_topc @ A ) =>
% 41.95/42.12       ( ![B:$i]:
% 41.95/42.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.95/42.12           ( ![C:$i]:
% 41.95/42.12             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 41.95/42.12               ( r1_tarski @
% 41.95/42.12                 ( k2_pre_topc @
% 41.95/42.12                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 41.95/42.12                 ( k9_subset_1 @
% 41.95/42.12                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 41.95/42.12                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 41.95/42.12  thf('65', plain,
% 41.95/42.12      (![X18 : $i, X19 : $i, X20 : $i]:
% 41.95/42.12         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 41.95/42.12          | (r1_tarski @ 
% 41.95/42.12             (k2_pre_topc @ X19 @ 
% 41.95/42.12              (k9_subset_1 @ (u1_struct_0 @ X19) @ X18 @ X20)) @ 
% 41.95/42.12             (k9_subset_1 @ (u1_struct_0 @ X19) @ (k2_pre_topc @ X19 @ X18) @ 
% 41.95/42.12              (k2_pre_topc @ X19 @ X20)))
% 41.95/42.12          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 41.95/42.12          | ~ (l1_pre_topc @ X19))),
% 41.95/42.12      inference('cnf', [status(esa)], [t51_pre_topc])).
% 41.95/42.12  thf('66', plain,
% 41.95/42.12      (![X0 : $i]:
% 41.95/42.12         (~ (l1_pre_topc @ sk_A)
% 41.95/42.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.95/42.12          | (r1_tarski @ 
% 41.95/42.12             (k2_pre_topc @ sk_A @ 
% 41.95/42.12              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.95/42.12               (k2_pre_topc @ sk_A @ sk_B) @ X0)) @ 
% 41.95/42.12             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.95/42.12              (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 41.95/42.12              (k2_pre_topc @ sk_A @ X0))))),
% 41.95/42.12      inference('sup-', [status(thm)], ['64', '65'])).
% 41.95/42.12  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 41.95/42.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.95/42.12  thf('68', plain,
% 41.95/42.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.95/42.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.95/42.12  thf(projectivity_k2_pre_topc, axiom,
% 41.95/42.12    (![A:$i,B:$i]:
% 41.95/42.12     ( ( ( l1_pre_topc @ A ) & 
% 41.95/42.12         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 41.95/42.12       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 41.95/42.12         ( k2_pre_topc @ A @ B ) ) ))).
% 41.95/42.12  thf('69', plain,
% 41.95/42.12      (![X16 : $i, X17 : $i]:
% 41.95/42.12         (~ (l1_pre_topc @ X16)
% 41.95/42.12          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 41.95/42.12          | ((k2_pre_topc @ X16 @ (k2_pre_topc @ X16 @ X17))
% 41.95/42.12              = (k2_pre_topc @ X16 @ X17)))),
% 41.95/42.12      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 41.95/42.12  thf('70', plain,
% 41.95/42.12      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 41.95/42.12          = (k2_pre_topc @ sk_A @ sk_B))
% 41.95/42.12        | ~ (l1_pre_topc @ sk_A))),
% 41.95/42.12      inference('sup-', [status(thm)], ['68', '69'])).
% 41.95/42.12  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 41.95/42.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.95/42.12  thf('72', plain,
% 41.95/42.12      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 41.95/42.12         = (k2_pre_topc @ sk_A @ sk_B))),
% 41.95/42.12      inference('demod', [status(thm)], ['70', '71'])).
% 41.95/42.12  thf('73', plain,
% 41.95/42.12      (![X0 : $i]:
% 41.95/42.12         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 41.95/42.12          | (r1_tarski @ 
% 41.95/42.12             (k2_pre_topc @ sk_A @ 
% 41.95/42.12              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.95/42.12               (k2_pre_topc @ sk_A @ sk_B) @ X0)) @ 
% 41.95/42.12             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.95/42.12              (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 41.95/42.12      inference('demod', [status(thm)], ['66', '67', '72'])).
% 41.95/42.12  thf('74', plain,
% 41.95/42.12      ((r1_tarski @ 
% 41.95/42.12        (k2_pre_topc @ sk_A @ 
% 41.95/42.12         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 41.95/42.12          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))) @ 
% 41.95/42.12        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 41.95/42.12         (k2_pre_topc @ sk_A @ 
% 41.95/42.12          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 41.95/42.12      inference('sup-', [status(thm)], ['59', '73'])).
% 41.95/42.12  thf('75', plain,
% 41.95/42.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.95/42.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.95/42.12  thf('76', plain,
% 41.95/42.12      (![X21 : $i, X22 : $i]:
% 41.95/42.12         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 41.95/42.12          | ((k2_tops_1 @ X22 @ X21)
% 41.95/42.12              = (k9_subset_1 @ (u1_struct_0 @ X22) @ 
% 41.95/42.12                 (k2_pre_topc @ X22 @ X21) @ 
% 41.95/42.12                 (k2_pre_topc @ X22 @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21))))
% 41.95/42.12          | ~ (l1_pre_topc @ X22))),
% 41.95/42.12      inference('cnf', [status(esa)], [d2_tops_1])).
% 41.95/42.12  thf('77', plain,
% 41.95/42.12      ((~ (l1_pre_topc @ sk_A)
% 41.95/42.12        | ((k2_tops_1 @ sk_A @ sk_B)
% 41.95/42.12            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 41.95/42.12               (k2_pre_topc @ sk_A @ sk_B) @ 
% 41.95/42.12               (k2_pre_topc @ sk_A @ 
% 41.95/42.12                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 41.95/42.12      inference('sup-', [status(thm)], ['75', '76'])).
% 41.95/42.12  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 41.95/42.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.95/42.12  thf('79', plain,
% 41.95/42.12      (((k2_tops_1 @ sk_A @ sk_B)
% 41.95/42.12         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 41.95/42.12            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 41.95/42.12      inference('demod', [status(thm)], ['77', '78'])).
% 41.95/42.12  thf('80', plain,
% 41.95/42.12      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 41.95/42.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 41.95/42.12      inference('sup-', [status(thm)], ['53', '54'])).
% 41.95/42.12  thf('81', plain,
% 41.95/42.12      (![X16 : $i, X17 : $i]:
% 41.95/42.12         (~ (l1_pre_topc @ X16)
% 41.95/42.12          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 41.95/42.12          | ((k2_pre_topc @ X16 @ (k2_pre_topc @ X16 @ X17))
% 41.95/42.12              = (k2_pre_topc @ X16 @ X17)))),
% 41.95/42.12      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 41.95/42.12  thf('82', plain,
% 41.95/42.12      ((((k2_pre_topc @ sk_A @ 
% 41.95/42.12          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 41.95/42.12          = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 41.95/42.12        | ~ (l1_pre_topc @ sk_A))),
% 41.95/42.12      inference('sup-', [status(thm)], ['80', '81'])).
% 41.95/42.12  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 41.95/42.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.95/42.12  thf('84', plain,
% 41.95/42.12      (((k2_pre_topc @ sk_A @ 
% 41.95/42.12         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 41.95/42.12         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 41.95/42.12      inference('demod', [status(thm)], ['82', '83'])).
% 41.95/42.12  thf('85', plain,
% 41.95/42.12      (((k2_tops_1 @ sk_A @ sk_B)
% 41.95/42.12         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 41.95/42.12            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 41.95/42.12      inference('demod', [status(thm)], ['77', '78'])).
% 41.95/42.12  thf('86', plain,
% 41.95/42.12      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.95/42.12        (k2_tops_1 @ sk_A @ sk_B))),
% 41.95/42.12      inference('demod', [status(thm)], ['74', '79', '84', '85'])).
% 41.95/42.12  thf('87', plain,
% 41.95/42.12      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 41.95/42.12         = (k2_tops_1 @ sk_A @ sk_B))),
% 41.95/42.12      inference('demod', [status(thm)], ['52', '86'])).
% 41.95/42.12  thf('88', plain,
% 41.95/42.12      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 41.95/42.12        (k2_tops_1 @ sk_A @ sk_B))),
% 41.95/42.12      inference('demod', [status(thm)], ['34', '87'])).
% 41.95/42.12  thf('89', plain, ($false), inference('demod', [status(thm)], ['0', '88'])).
% 41.95/42.12  
% 41.95/42.12  % SZS output end Refutation
% 41.95/42.12  
% 41.95/42.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
