%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SiE4OpuMMW

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:12 EST 2020

% Result     : Theorem 14.46s
% Output     : Refutation 14.46s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 209 expanded)
%              Number of leaves         :   22 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          : 1109 (2570 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X9 @ X10 ) @ ( k3_subset_1 @ X9 @ ( k9_subset_1 @ X9 @ X10 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_tops_1 @ X21 @ X20 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ X20 ) @ ( k2_pre_topc @ X21 @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
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

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_tarski @ X15 @ ( k2_pre_topc @ X16 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('44',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t51_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ X18 @ ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ X19 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_pre_topc @ X18 @ X17 ) @ ( k2_pre_topc @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t51_pre_topc])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k2_pre_topc @ X13 @ ( k2_pre_topc @ X13 @ X14 ) )
        = ( k2_pre_topc @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('59',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['55','56','61'])).

thf('63',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['48','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_tops_1 @ X21 @ X20 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ X20 ) @ ( k2_pre_topc @ X21 @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('70',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k2_pre_topc @ X13 @ ( k2_pre_topc @ X13 @ X14 ) )
        = ( k2_pre_topc @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('71',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('75',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','68','73','74'])).

thf('76',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['41','75'])).

thf('77',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SiE4OpuMMW
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 14.46/14.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.46/14.68  % Solved by: fo/fo7.sh
% 14.46/14.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.46/14.68  % done 2663 iterations in 14.221s
% 14.46/14.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.46/14.68  % SZS output start Refutation
% 14.46/14.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.46/14.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 14.46/14.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 14.46/14.68  thf(sk_A_type, type, sk_A: $i).
% 14.46/14.68  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 14.46/14.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.46/14.68  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 14.46/14.68  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 14.46/14.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 14.46/14.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 14.46/14.68  thf(sk_B_type, type, sk_B: $i).
% 14.46/14.68  thf(t68_tops_1, conjecture,
% 14.46/14.68    (![A:$i]:
% 14.46/14.68     ( ( l1_pre_topc @ A ) =>
% 14.46/14.68       ( ![B:$i]:
% 14.46/14.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.46/14.68           ( r1_tarski @
% 14.46/14.68             ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 14.46/14.68  thf(zf_stmt_0, negated_conjecture,
% 14.46/14.68    (~( ![A:$i]:
% 14.46/14.68        ( ( l1_pre_topc @ A ) =>
% 14.46/14.68          ( ![B:$i]:
% 14.46/14.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.46/14.68              ( r1_tarski @
% 14.46/14.68                ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) @ 
% 14.46/14.68                ( k2_tops_1 @ A @ B ) ) ) ) ) )),
% 14.46/14.68    inference('cnf.neg', [status(esa)], [t68_tops_1])).
% 14.46/14.68  thf('0', plain,
% 14.46/14.68      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68          (k2_tops_1 @ sk_A @ sk_B))),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('1', plain,
% 14.46/14.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf(dt_k2_tops_1, axiom,
% 14.46/14.68    (![A:$i,B:$i]:
% 14.46/14.68     ( ( ( l1_pre_topc @ A ) & 
% 14.46/14.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 14.46/14.68       ( m1_subset_1 @
% 14.46/14.68         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 14.46/14.68  thf('2', plain,
% 14.46/14.68      (![X22 : $i, X23 : $i]:
% 14.46/14.68         (~ (l1_pre_topc @ X22)
% 14.46/14.68          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 14.46/14.68          | (m1_subset_1 @ (k2_tops_1 @ X22 @ X23) @ 
% 14.46/14.68             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 14.46/14.68      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 14.46/14.68  thf('3', plain,
% 14.46/14.68      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 14.46/14.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.46/14.68        | ~ (l1_pre_topc @ sk_A))),
% 14.46/14.68      inference('sup-', [status(thm)], ['1', '2'])).
% 14.46/14.68  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('5', plain,
% 14.46/14.68      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 14.46/14.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('demod', [status(thm)], ['3', '4'])).
% 14.46/14.68  thf(dt_k2_pre_topc, axiom,
% 14.46/14.68    (![A:$i,B:$i]:
% 14.46/14.68     ( ( ( l1_pre_topc @ A ) & 
% 14.46/14.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 14.46/14.68       ( m1_subset_1 @
% 14.46/14.68         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 14.46/14.68  thf('6', plain,
% 14.46/14.68      (![X11 : $i, X12 : $i]:
% 14.46/14.68         (~ (l1_pre_topc @ X11)
% 14.46/14.68          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 14.46/14.68          | (m1_subset_1 @ (k2_pre_topc @ X11 @ X12) @ 
% 14.46/14.68             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 14.46/14.68      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 14.46/14.68  thf('7', plain,
% 14.46/14.68      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.46/14.68        | ~ (l1_pre_topc @ sk_A))),
% 14.46/14.68      inference('sup-', [status(thm)], ['5', '6'])).
% 14.46/14.68  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('9', plain,
% 14.46/14.68      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('demod', [status(thm)], ['7', '8'])).
% 14.46/14.68  thf('10', plain,
% 14.46/14.68      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 14.46/14.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('demod', [status(thm)], ['3', '4'])).
% 14.46/14.68  thf(dt_k3_subset_1, axiom,
% 14.46/14.68    (![A:$i,B:$i]:
% 14.46/14.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 14.46/14.68       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 14.46/14.68  thf('11', plain,
% 14.46/14.68      (![X3 : $i, X4 : $i]:
% 14.46/14.68         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 14.46/14.68          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 14.46/14.68      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 14.46/14.68  thf('12', plain,
% 14.46/14.68      ((m1_subset_1 @ 
% 14.46/14.68        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('sup-', [status(thm)], ['10', '11'])).
% 14.46/14.68  thf('13', plain,
% 14.46/14.68      (![X11 : $i, X12 : $i]:
% 14.46/14.68         (~ (l1_pre_topc @ X11)
% 14.46/14.68          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 14.46/14.68          | (m1_subset_1 @ (k2_pre_topc @ X11 @ X12) @ 
% 14.46/14.68             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 14.46/14.68      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 14.46/14.68  thf('14', plain,
% 14.46/14.68      (((m1_subset_1 @ 
% 14.46/14.68         (k2_pre_topc @ sk_A @ 
% 14.46/14.68          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 14.46/14.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.46/14.68        | ~ (l1_pre_topc @ sk_A))),
% 14.46/14.68      inference('sup-', [status(thm)], ['12', '13'])).
% 14.46/14.68  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('16', plain,
% 14.46/14.68      ((m1_subset_1 @ 
% 14.46/14.68        (k2_pre_topc @ sk_A @ 
% 14.46/14.68         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 14.46/14.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('demod', [status(thm)], ['14', '15'])).
% 14.46/14.68  thf(t42_subset_1, axiom,
% 14.46/14.68    (![A:$i,B:$i]:
% 14.46/14.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 14.46/14.68       ( ![C:$i]:
% 14.46/14.68         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 14.46/14.68           ( r1_tarski @
% 14.46/14.68             ( k3_subset_1 @ A @ B ) @ 
% 14.46/14.68             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 14.46/14.68  thf('17', plain,
% 14.46/14.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 14.46/14.68         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 14.46/14.68          | (r1_tarski @ (k3_subset_1 @ X9 @ X10) @ 
% 14.46/14.68             (k3_subset_1 @ X9 @ (k9_subset_1 @ X9 @ X10 @ X8)))
% 14.46/14.68          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 14.46/14.68      inference('cnf', [status(esa)], [t42_subset_1])).
% 14.46/14.68  thf('18', plain,
% 14.46/14.68      (![X0 : $i]:
% 14.46/14.68         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.46/14.68          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 14.46/14.68             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 14.46/14.68              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 14.46/14.68               (k2_pre_topc @ sk_A @ 
% 14.46/14.68                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))))))),
% 14.46/14.68      inference('sup-', [status(thm)], ['16', '17'])).
% 14.46/14.68  thf('19', plain,
% 14.46/14.68      ((r1_tarski @ 
% 14.46/14.68        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 14.46/14.68         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 14.46/14.68        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 14.46/14.68         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 14.46/14.68          (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68          (k2_pre_topc @ sk_A @ 
% 14.46/14.68           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 14.46/14.68      inference('sup-', [status(thm)], ['9', '18'])).
% 14.46/14.68  thf('20', plain,
% 14.46/14.68      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 14.46/14.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('demod', [status(thm)], ['3', '4'])).
% 14.46/14.68  thf(d2_tops_1, axiom,
% 14.46/14.68    (![A:$i]:
% 14.46/14.68     ( ( l1_pre_topc @ A ) =>
% 14.46/14.68       ( ![B:$i]:
% 14.46/14.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.46/14.68           ( ( k2_tops_1 @ A @ B ) =
% 14.46/14.68             ( k9_subset_1 @
% 14.46/14.68               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 14.46/14.68               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 14.46/14.68  thf('21', plain,
% 14.46/14.68      (![X20 : $i, X21 : $i]:
% 14.46/14.68         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 14.46/14.68          | ((k2_tops_1 @ X21 @ X20)
% 14.46/14.68              = (k9_subset_1 @ (u1_struct_0 @ X21) @ 
% 14.46/14.68                 (k2_pre_topc @ X21 @ X20) @ 
% 14.46/14.68                 (k2_pre_topc @ X21 @ (k3_subset_1 @ (u1_struct_0 @ X21) @ X20))))
% 14.46/14.68          | ~ (l1_pre_topc @ X21))),
% 14.46/14.68      inference('cnf', [status(esa)], [d2_tops_1])).
% 14.46/14.68  thf('22', plain,
% 14.46/14.68      ((~ (l1_pre_topc @ sk_A)
% 14.46/14.68        | ((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 14.46/14.68            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 14.46/14.68               (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68               (k2_pre_topc @ sk_A @ 
% 14.46/14.68                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 14.46/14.68      inference('sup-', [status(thm)], ['20', '21'])).
% 14.46/14.68  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('24', plain,
% 14.46/14.68      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 14.46/14.68         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 14.46/14.68            (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68            (k2_pre_topc @ sk_A @ 
% 14.46/14.68             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 14.46/14.68      inference('demod', [status(thm)], ['22', '23'])).
% 14.46/14.68  thf('25', plain,
% 14.46/14.68      ((r1_tarski @ 
% 14.46/14.68        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 14.46/14.68         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 14.46/14.68        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 14.46/14.68         (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 14.46/14.68      inference('demod', [status(thm)], ['19', '24'])).
% 14.46/14.68  thf(t31_subset_1, axiom,
% 14.46/14.68    (![A:$i,B:$i]:
% 14.46/14.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 14.46/14.68       ( ![C:$i]:
% 14.46/14.68         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 14.46/14.68           ( ( r1_tarski @ B @ C ) <=>
% 14.46/14.68             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 14.46/14.68  thf('26', plain,
% 14.46/14.68      (![X5 : $i, X6 : $i, X7 : $i]:
% 14.46/14.68         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 14.46/14.68          | ~ (r1_tarski @ (k3_subset_1 @ X6 @ X5) @ (k3_subset_1 @ X6 @ X7))
% 14.46/14.68          | (r1_tarski @ X7 @ X5)
% 14.46/14.68          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 14.46/14.68      inference('cnf', [status(esa)], [t31_subset_1])).
% 14.46/14.68  thf('27', plain,
% 14.46/14.68      ((~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.46/14.68        | (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68           (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 14.46/14.68        | ~ (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 14.46/14.68      inference('sup-', [status(thm)], ['25', '26'])).
% 14.46/14.68  thf('28', plain,
% 14.46/14.68      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 14.46/14.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('demod', [status(thm)], ['3', '4'])).
% 14.46/14.68  thf('29', plain,
% 14.46/14.68      (![X22 : $i, X23 : $i]:
% 14.46/14.68         (~ (l1_pre_topc @ X22)
% 14.46/14.68          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 14.46/14.68          | (m1_subset_1 @ (k2_tops_1 @ X22 @ X23) @ 
% 14.46/14.68             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 14.46/14.68      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 14.46/14.68  thf('30', plain,
% 14.46/14.68      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.46/14.68        | ~ (l1_pre_topc @ sk_A))),
% 14.46/14.68      inference('sup-', [status(thm)], ['28', '29'])).
% 14.46/14.68  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('32', plain,
% 14.46/14.68      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('demod', [status(thm)], ['30', '31'])).
% 14.46/14.68  thf('33', plain,
% 14.46/14.68      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('demod', [status(thm)], ['7', '8'])).
% 14.46/14.68  thf('34', plain,
% 14.46/14.68      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68        (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 14.46/14.68      inference('demod', [status(thm)], ['27', '32', '33'])).
% 14.46/14.68  thf('35', plain,
% 14.46/14.68      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 14.46/14.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('demod', [status(thm)], ['3', '4'])).
% 14.46/14.68  thf(t48_pre_topc, axiom,
% 14.46/14.68    (![A:$i]:
% 14.46/14.68     ( ( l1_pre_topc @ A ) =>
% 14.46/14.68       ( ![B:$i]:
% 14.46/14.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.46/14.68           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 14.46/14.68  thf('36', plain,
% 14.46/14.68      (![X15 : $i, X16 : $i]:
% 14.46/14.68         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 14.46/14.68          | (r1_tarski @ X15 @ (k2_pre_topc @ X16 @ X15))
% 14.46/14.68          | ~ (l1_pre_topc @ X16))),
% 14.46/14.68      inference('cnf', [status(esa)], [t48_pre_topc])).
% 14.46/14.68  thf('37', plain,
% 14.46/14.68      ((~ (l1_pre_topc @ sk_A)
% 14.46/14.68        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 14.46/14.68           (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 14.46/14.68      inference('sup-', [status(thm)], ['35', '36'])).
% 14.46/14.68  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('39', plain,
% 14.46/14.68      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 14.46/14.68        (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 14.46/14.68      inference('demod', [status(thm)], ['37', '38'])).
% 14.46/14.68  thf(d10_xboole_0, axiom,
% 14.46/14.68    (![A:$i,B:$i]:
% 14.46/14.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 14.46/14.68  thf('40', plain,
% 14.46/14.68      (![X0 : $i, X2 : $i]:
% 14.46/14.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 14.46/14.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.46/14.68  thf('41', plain,
% 14.46/14.68      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68           (k2_tops_1 @ sk_A @ sk_B))
% 14.46/14.68        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 14.46/14.68            = (k2_tops_1 @ sk_A @ sk_B)))),
% 14.46/14.68      inference('sup-', [status(thm)], ['39', '40'])).
% 14.46/14.68  thf('42', plain,
% 14.46/14.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('43', plain,
% 14.46/14.68      (![X3 : $i, X4 : $i]:
% 14.46/14.68         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 14.46/14.68          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 14.46/14.68      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 14.46/14.68  thf('44', plain,
% 14.46/14.68      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 14.46/14.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('sup-', [status(thm)], ['42', '43'])).
% 14.46/14.68  thf('45', plain,
% 14.46/14.68      (![X11 : $i, X12 : $i]:
% 14.46/14.68         (~ (l1_pre_topc @ X11)
% 14.46/14.68          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 14.46/14.68          | (m1_subset_1 @ (k2_pre_topc @ X11 @ X12) @ 
% 14.46/14.68             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 14.46/14.68      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 14.46/14.68  thf('46', plain,
% 14.46/14.68      (((m1_subset_1 @ 
% 14.46/14.68         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 14.46/14.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.46/14.68        | ~ (l1_pre_topc @ sk_A))),
% 14.46/14.68      inference('sup-', [status(thm)], ['44', '45'])).
% 14.46/14.68  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('48', plain,
% 14.46/14.68      ((m1_subset_1 @ 
% 14.46/14.68        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 14.46/14.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('demod', [status(thm)], ['46', '47'])).
% 14.46/14.68  thf('49', plain,
% 14.46/14.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('50', plain,
% 14.46/14.68      (![X11 : $i, X12 : $i]:
% 14.46/14.68         (~ (l1_pre_topc @ X11)
% 14.46/14.68          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 14.46/14.68          | (m1_subset_1 @ (k2_pre_topc @ X11 @ X12) @ 
% 14.46/14.68             (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 14.46/14.68      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 14.46/14.68  thf('51', plain,
% 14.46/14.68      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 14.46/14.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.46/14.68        | ~ (l1_pre_topc @ sk_A))),
% 14.46/14.68      inference('sup-', [status(thm)], ['49', '50'])).
% 14.46/14.68  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('53', plain,
% 14.46/14.68      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 14.46/14.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('demod', [status(thm)], ['51', '52'])).
% 14.46/14.68  thf(t51_pre_topc, axiom,
% 14.46/14.68    (![A:$i]:
% 14.46/14.68     ( ( l1_pre_topc @ A ) =>
% 14.46/14.68       ( ![B:$i]:
% 14.46/14.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.46/14.68           ( ![C:$i]:
% 14.46/14.68             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.46/14.68               ( r1_tarski @
% 14.46/14.68                 ( k2_pre_topc @
% 14.46/14.68                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 14.46/14.68                 ( k9_subset_1 @
% 14.46/14.68                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 14.46/14.68                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 14.46/14.68  thf('54', plain,
% 14.46/14.68      (![X17 : $i, X18 : $i, X19 : $i]:
% 14.46/14.68         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 14.46/14.68          | (r1_tarski @ 
% 14.46/14.68             (k2_pre_topc @ X18 @ 
% 14.46/14.68              (k9_subset_1 @ (u1_struct_0 @ X18) @ X17 @ X19)) @ 
% 14.46/14.68             (k9_subset_1 @ (u1_struct_0 @ X18) @ (k2_pre_topc @ X18 @ X17) @ 
% 14.46/14.68              (k2_pre_topc @ X18 @ X19)))
% 14.46/14.68          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 14.46/14.68          | ~ (l1_pre_topc @ X18))),
% 14.46/14.68      inference('cnf', [status(esa)], [t51_pre_topc])).
% 14.46/14.68  thf('55', plain,
% 14.46/14.68      (![X0 : $i]:
% 14.46/14.68         (~ (l1_pre_topc @ sk_A)
% 14.46/14.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.46/14.68          | (r1_tarski @ 
% 14.46/14.68             (k2_pre_topc @ sk_A @ 
% 14.46/14.68              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 14.46/14.68               (k2_pre_topc @ sk_A @ sk_B) @ X0)) @ 
% 14.46/14.68             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 14.46/14.68              (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 14.46/14.68              (k2_pre_topc @ sk_A @ X0))))),
% 14.46/14.68      inference('sup-', [status(thm)], ['53', '54'])).
% 14.46/14.68  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('57', plain,
% 14.46/14.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf(projectivity_k2_pre_topc, axiom,
% 14.46/14.68    (![A:$i,B:$i]:
% 14.46/14.68     ( ( ( l1_pre_topc @ A ) & 
% 14.46/14.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 14.46/14.68       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 14.46/14.68         ( k2_pre_topc @ A @ B ) ) ))).
% 14.46/14.68  thf('58', plain,
% 14.46/14.68      (![X13 : $i, X14 : $i]:
% 14.46/14.68         (~ (l1_pre_topc @ X13)
% 14.46/14.68          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 14.46/14.68          | ((k2_pre_topc @ X13 @ (k2_pre_topc @ X13 @ X14))
% 14.46/14.68              = (k2_pre_topc @ X13 @ X14)))),
% 14.46/14.68      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 14.46/14.68  thf('59', plain,
% 14.46/14.68      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 14.46/14.68          = (k2_pre_topc @ sk_A @ sk_B))
% 14.46/14.68        | ~ (l1_pre_topc @ sk_A))),
% 14.46/14.68      inference('sup-', [status(thm)], ['57', '58'])).
% 14.46/14.68  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('61', plain,
% 14.46/14.68      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 14.46/14.68         = (k2_pre_topc @ sk_A @ sk_B))),
% 14.46/14.68      inference('demod', [status(thm)], ['59', '60'])).
% 14.46/14.68  thf('62', plain,
% 14.46/14.68      (![X0 : $i]:
% 14.46/14.68         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.46/14.68          | (r1_tarski @ 
% 14.46/14.68             (k2_pre_topc @ sk_A @ 
% 14.46/14.68              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 14.46/14.68               (k2_pre_topc @ sk_A @ sk_B) @ X0)) @ 
% 14.46/14.68             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 14.46/14.68              (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 14.46/14.68      inference('demod', [status(thm)], ['55', '56', '61'])).
% 14.46/14.68  thf('63', plain,
% 14.46/14.68      ((r1_tarski @ 
% 14.46/14.68        (k2_pre_topc @ sk_A @ 
% 14.46/14.68         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 14.46/14.68          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))) @ 
% 14.46/14.68        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 14.46/14.68         (k2_pre_topc @ sk_A @ 
% 14.46/14.68          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 14.46/14.68      inference('sup-', [status(thm)], ['48', '62'])).
% 14.46/14.68  thf('64', plain,
% 14.46/14.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('65', plain,
% 14.46/14.68      (![X20 : $i, X21 : $i]:
% 14.46/14.68         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 14.46/14.68          | ((k2_tops_1 @ X21 @ X20)
% 14.46/14.68              = (k9_subset_1 @ (u1_struct_0 @ X21) @ 
% 14.46/14.68                 (k2_pre_topc @ X21 @ X20) @ 
% 14.46/14.68                 (k2_pre_topc @ X21 @ (k3_subset_1 @ (u1_struct_0 @ X21) @ X20))))
% 14.46/14.68          | ~ (l1_pre_topc @ X21))),
% 14.46/14.68      inference('cnf', [status(esa)], [d2_tops_1])).
% 14.46/14.68  thf('66', plain,
% 14.46/14.68      ((~ (l1_pre_topc @ sk_A)
% 14.46/14.68        | ((k2_tops_1 @ sk_A @ sk_B)
% 14.46/14.68            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 14.46/14.68               (k2_pre_topc @ sk_A @ sk_B) @ 
% 14.46/14.68               (k2_pre_topc @ sk_A @ 
% 14.46/14.68                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 14.46/14.68      inference('sup-', [status(thm)], ['64', '65'])).
% 14.46/14.68  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('68', plain,
% 14.46/14.68      (((k2_tops_1 @ sk_A @ sk_B)
% 14.46/14.68         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 14.46/14.68            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 14.46/14.68      inference('demod', [status(thm)], ['66', '67'])).
% 14.46/14.68  thf('69', plain,
% 14.46/14.68      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 14.46/14.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.46/14.68      inference('sup-', [status(thm)], ['42', '43'])).
% 14.46/14.68  thf('70', plain,
% 14.46/14.68      (![X13 : $i, X14 : $i]:
% 14.46/14.68         (~ (l1_pre_topc @ X13)
% 14.46/14.68          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 14.46/14.68          | ((k2_pre_topc @ X13 @ (k2_pre_topc @ X13 @ X14))
% 14.46/14.68              = (k2_pre_topc @ X13 @ X14)))),
% 14.46/14.68      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 14.46/14.68  thf('71', plain,
% 14.46/14.68      ((((k2_pre_topc @ sk_A @ 
% 14.46/14.68          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 14.46/14.68          = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 14.46/14.68        | ~ (l1_pre_topc @ sk_A))),
% 14.46/14.68      inference('sup-', [status(thm)], ['69', '70'])).
% 14.46/14.68  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 14.46/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.46/14.68  thf('73', plain,
% 14.46/14.68      (((k2_pre_topc @ sk_A @ 
% 14.46/14.68         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 14.46/14.68         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 14.46/14.68      inference('demod', [status(thm)], ['71', '72'])).
% 14.46/14.68  thf('74', plain,
% 14.46/14.68      (((k2_tops_1 @ sk_A @ sk_B)
% 14.46/14.68         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 14.46/14.68            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 14.46/14.68      inference('demod', [status(thm)], ['66', '67'])).
% 14.46/14.68  thf('75', plain,
% 14.46/14.68      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68        (k2_tops_1 @ sk_A @ sk_B))),
% 14.46/14.68      inference('demod', [status(thm)], ['63', '68', '73', '74'])).
% 14.46/14.68  thf('76', plain,
% 14.46/14.68      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))
% 14.46/14.68         = (k2_tops_1 @ sk_A @ sk_B))),
% 14.46/14.68      inference('demod', [status(thm)], ['41', '75'])).
% 14.46/14.68  thf('77', plain,
% 14.46/14.68      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 14.46/14.68        (k2_tops_1 @ sk_A @ sk_B))),
% 14.46/14.68      inference('demod', [status(thm)], ['34', '76'])).
% 14.46/14.68  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 14.46/14.68  
% 14.46/14.68  % SZS output end Refutation
% 14.46/14.68  
% 14.46/14.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
