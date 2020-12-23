%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pc57zUyAOm

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:18 EST 2020

% Result     : Theorem 8.23s
% Output     : Refutation 8.23s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 134 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  720 (1459 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(t73_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_tops_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('8',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t41_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X9 @ ( k4_subset_1 @ X9 @ X10 @ X8 ) ) @ ( k3_subset_1 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('13',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( ( k4_subset_1 @ X1 @ X0 @ X2 )
        = ( k4_subset_1 @ X1 @ X2 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ ( k2_tops_1 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_tops_1 @ X21 @ X20 )
        = ( k2_tops_1 @ X21 @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','25'])).

thf('27',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k1_tops_1 @ X17 @ X16 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k2_pre_topc @ X17 @ ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','27','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X13 @ ( k3_subset_1 @ X12 @ X11 ) )
      | ( r1_xboole_0 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('44',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('46',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['37','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pc57zUyAOm
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.23/8.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.23/8.45  % Solved by: fo/fo7.sh
% 8.23/8.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.23/8.45  % done 2274 iterations in 7.992s
% 8.23/8.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.23/8.45  % SZS output start Refutation
% 8.23/8.45  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 8.23/8.45  thf(sk_A_type, type, sk_A: $i).
% 8.23/8.45  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 8.23/8.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.23/8.45  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 8.23/8.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.23/8.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.23/8.45  thf(sk_B_type, type, sk_B: $i).
% 8.23/8.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.23/8.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.23/8.45  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 8.23/8.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.23/8.45  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 8.23/8.45  thf(t73_tops_1, conjecture,
% 8.23/8.45    (![A:$i]:
% 8.23/8.45     ( ( l1_pre_topc @ A ) =>
% 8.23/8.45       ( ![B:$i]:
% 8.23/8.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.23/8.45           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 8.23/8.45  thf(zf_stmt_0, negated_conjecture,
% 8.23/8.45    (~( ![A:$i]:
% 8.23/8.45        ( ( l1_pre_topc @ A ) =>
% 8.23/8.45          ( ![B:$i]:
% 8.23/8.45            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.23/8.45              ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ) )),
% 8.23/8.45    inference('cnf.neg', [status(esa)], [t73_tops_1])).
% 8.23/8.45  thf('0', plain,
% 8.23/8.45      (~ (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 8.23/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.45  thf('1', plain,
% 8.23/8.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.45  thf(dt_k2_tops_1, axiom,
% 8.23/8.45    (![A:$i,B:$i]:
% 8.23/8.45     ( ( ( l1_pre_topc @ A ) & 
% 8.23/8.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.23/8.45       ( m1_subset_1 @
% 8.23/8.45         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 8.23/8.45  thf('2', plain,
% 8.23/8.45      (![X18 : $i, X19 : $i]:
% 8.23/8.45         (~ (l1_pre_topc @ X18)
% 8.23/8.45          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 8.23/8.45          | (m1_subset_1 @ (k2_tops_1 @ X18 @ X19) @ 
% 8.23/8.45             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 8.23/8.45      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 8.23/8.45  thf('3', plain,
% 8.23/8.45      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.45         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.23/8.45        | ~ (l1_pre_topc @ sk_A))),
% 8.23/8.45      inference('sup-', [status(thm)], ['1', '2'])).
% 8.23/8.45  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 8.23/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.45  thf('5', plain,
% 8.23/8.45      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.45      inference('demod', [status(thm)], ['3', '4'])).
% 8.23/8.45  thf('6', plain,
% 8.23/8.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.45  thf(dt_k3_subset_1, axiom,
% 8.23/8.45    (![A:$i,B:$i]:
% 8.23/8.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.23/8.45       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 8.23/8.45  thf('7', plain,
% 8.23/8.45      (![X3 : $i, X4 : $i]:
% 8.23/8.45         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 8.23/8.45          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 8.23/8.45      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 8.23/8.45  thf('8', plain,
% 8.23/8.45      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 8.23/8.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.45      inference('sup-', [status(thm)], ['6', '7'])).
% 8.23/8.45  thf(t41_subset_1, axiom,
% 8.23/8.45    (![A:$i,B:$i]:
% 8.23/8.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.23/8.45       ( ![C:$i]:
% 8.23/8.45         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 8.23/8.45           ( r1_tarski @
% 8.23/8.45             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 8.23/8.45             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 8.23/8.45  thf('9', plain,
% 8.23/8.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.23/8.45         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 8.23/8.45          | (r1_tarski @ (k3_subset_1 @ X9 @ (k4_subset_1 @ X9 @ X10 @ X8)) @ 
% 8.23/8.45             (k3_subset_1 @ X9 @ X10))
% 8.23/8.45          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 8.23/8.45      inference('cnf', [status(esa)], [t41_subset_1])).
% 8.23/8.45  thf('10', plain,
% 8.23/8.45      (![X0 : $i]:
% 8.23/8.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.23/8.45          | (r1_tarski @ 
% 8.23/8.45             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.45              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 8.23/8.45               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 8.23/8.45             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 8.23/8.45      inference('sup-', [status(thm)], ['8', '9'])).
% 8.23/8.45  thf('11', plain,
% 8.23/8.45      ((r1_tarski @ 
% 8.23/8.45        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.45         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.45          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 8.23/8.45        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 8.23/8.45      inference('sup-', [status(thm)], ['5', '10'])).
% 8.23/8.45  thf('12', plain,
% 8.23/8.45      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.45      inference('demod', [status(thm)], ['3', '4'])).
% 8.23/8.45  thf('13', plain,
% 8.23/8.45      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 8.23/8.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.45      inference('sup-', [status(thm)], ['6', '7'])).
% 8.23/8.45  thf(commutativity_k4_subset_1, axiom,
% 8.23/8.45    (![A:$i,B:$i,C:$i]:
% 8.23/8.45     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 8.23/8.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.23/8.45       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 8.23/8.45  thf('14', plain,
% 8.23/8.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.23/8.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 8.23/8.45          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1))
% 8.23/8.45          | ((k4_subset_1 @ X1 @ X0 @ X2) = (k4_subset_1 @ X1 @ X2 @ X0)))),
% 8.23/8.45      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 8.23/8.45  thf('15', plain,
% 8.23/8.45      (![X0 : $i]:
% 8.23/8.45         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.45            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 8.23/8.45            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 8.23/8.45               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 8.23/8.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.23/8.45      inference('sup-', [status(thm)], ['13', '14'])).
% 8.23/8.45  thf('16', plain,
% 8.23/8.45      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.45         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 8.23/8.45         (k2_tops_1 @ sk_A @ sk_B))
% 8.23/8.45         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.45            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 8.23/8.45      inference('sup-', [status(thm)], ['12', '15'])).
% 8.23/8.45  thf('17', plain,
% 8.23/8.45      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 8.23/8.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.45      inference('sup-', [status(thm)], ['6', '7'])).
% 8.23/8.45  thf(t65_tops_1, axiom,
% 8.23/8.45    (![A:$i]:
% 8.23/8.45     ( ( l1_pre_topc @ A ) =>
% 8.23/8.45       ( ![B:$i]:
% 8.23/8.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.23/8.45           ( ( k2_pre_topc @ A @ B ) =
% 8.23/8.45             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 8.23/8.45  thf('18', plain,
% 8.23/8.45      (![X22 : $i, X23 : $i]:
% 8.23/8.45         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 8.23/8.45          | ((k2_pre_topc @ X23 @ X22)
% 8.23/8.45              = (k4_subset_1 @ (u1_struct_0 @ X23) @ X22 @ 
% 8.23/8.45                 (k2_tops_1 @ X23 @ X22)))
% 8.23/8.45          | ~ (l1_pre_topc @ X23))),
% 8.23/8.45      inference('cnf', [status(esa)], [t65_tops_1])).
% 8.23/8.45  thf('19', plain,
% 8.23/8.45      ((~ (l1_pre_topc @ sk_A)
% 8.23/8.45        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 8.23/8.45            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.45               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 8.23/8.45               (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 8.23/8.45      inference('sup-', [status(thm)], ['17', '18'])).
% 8.23/8.45  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 8.23/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.45  thf('21', plain,
% 8.23/8.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.45  thf(t62_tops_1, axiom,
% 8.23/8.45    (![A:$i]:
% 8.23/8.45     ( ( l1_pre_topc @ A ) =>
% 8.23/8.45       ( ![B:$i]:
% 8.23/8.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.23/8.45           ( ( k2_tops_1 @ A @ B ) =
% 8.23/8.45             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 8.23/8.45  thf('22', plain,
% 8.23/8.45      (![X20 : $i, X21 : $i]:
% 8.23/8.45         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 8.23/8.45          | ((k2_tops_1 @ X21 @ X20)
% 8.23/8.45              = (k2_tops_1 @ X21 @ (k3_subset_1 @ (u1_struct_0 @ X21) @ X20)))
% 8.23/8.45          | ~ (l1_pre_topc @ X21))),
% 8.23/8.45      inference('cnf', [status(esa)], [t62_tops_1])).
% 8.23/8.45  thf('23', plain,
% 8.23/8.45      ((~ (l1_pre_topc @ sk_A)
% 8.23/8.45        | ((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.45            = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 8.23/8.45      inference('sup-', [status(thm)], ['21', '22'])).
% 8.23/8.45  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 8.23/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.45  thf('25', plain,
% 8.23/8.45      (((k2_tops_1 @ sk_A @ sk_B)
% 8.23/8.45         = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 8.23/8.45      inference('demod', [status(thm)], ['23', '24'])).
% 8.23/8.45  thf('26', plain,
% 8.23/8.45      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 8.23/8.45         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.45            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 8.23/8.45            (k2_tops_1 @ sk_A @ sk_B)))),
% 8.23/8.45      inference('demod', [status(thm)], ['19', '20', '25'])).
% 8.23/8.45  thf('27', plain,
% 8.23/8.45      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 8.23/8.45         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.45            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 8.23/8.45      inference('sup+', [status(thm)], ['16', '26'])).
% 8.23/8.45  thf('28', plain,
% 8.23/8.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.45  thf(d1_tops_1, axiom,
% 8.23/8.45    (![A:$i]:
% 8.23/8.45     ( ( l1_pre_topc @ A ) =>
% 8.23/8.45       ( ![B:$i]:
% 8.23/8.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.23/8.45           ( ( k1_tops_1 @ A @ B ) =
% 8.23/8.45             ( k3_subset_1 @
% 8.23/8.45               ( u1_struct_0 @ A ) @ 
% 8.23/8.45               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 8.23/8.45  thf('29', plain,
% 8.23/8.45      (![X16 : $i, X17 : $i]:
% 8.23/8.45         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 8.23/8.45          | ((k1_tops_1 @ X17 @ X16)
% 8.23/8.45              = (k3_subset_1 @ (u1_struct_0 @ X17) @ 
% 8.23/8.45                 (k2_pre_topc @ X17 @ (k3_subset_1 @ (u1_struct_0 @ X17) @ X16))))
% 8.23/8.45          | ~ (l1_pre_topc @ X17))),
% 8.23/8.45      inference('cnf', [status(esa)], [d1_tops_1])).
% 8.23/8.45  thf('30', plain,
% 8.23/8.45      ((~ (l1_pre_topc @ sk_A)
% 8.23/8.45        | ((k1_tops_1 @ sk_A @ sk_B)
% 8.23/8.45            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.45               (k2_pre_topc @ sk_A @ 
% 8.23/8.45                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 8.23/8.45      inference('sup-', [status(thm)], ['28', '29'])).
% 8.23/8.45  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 8.23/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.45  thf('32', plain,
% 8.23/8.45      (((k1_tops_1 @ sk_A @ sk_B)
% 8.23/8.45         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.45            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 8.23/8.45      inference('demod', [status(thm)], ['30', '31'])).
% 8.23/8.45  thf('33', plain,
% 8.23/8.45      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.45        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 8.23/8.45      inference('demod', [status(thm)], ['11', '27', '32'])).
% 8.23/8.45  thf('34', plain,
% 8.23/8.45      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.45      inference('demod', [status(thm)], ['3', '4'])).
% 8.23/8.45  thf(t43_subset_1, axiom,
% 8.23/8.45    (![A:$i,B:$i]:
% 8.23/8.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.23/8.45       ( ![C:$i]:
% 8.23/8.45         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 8.23/8.45           ( ( r1_xboole_0 @ B @ C ) <=>
% 8.23/8.45             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 8.23/8.45  thf('35', plain,
% 8.23/8.45      (![X11 : $i, X12 : $i, X13 : $i]:
% 8.23/8.45         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 8.23/8.45          | ~ (r1_tarski @ X13 @ (k3_subset_1 @ X12 @ X11))
% 8.23/8.45          | (r1_xboole_0 @ X13 @ X11)
% 8.23/8.45          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 8.23/8.45      inference('cnf', [status(esa)], [t43_subset_1])).
% 8.23/8.45  thf('36', plain,
% 8.23/8.45      (![X0 : $i]:
% 8.23/8.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.23/8.45          | (r1_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 8.23/8.45          | ~ (r1_tarski @ X0 @ 
% 8.23/8.45               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 8.23/8.45      inference('sup-', [status(thm)], ['34', '35'])).
% 8.23/8.45  thf('37', plain,
% 8.23/8.45      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 8.23/8.45        | ~ (m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.45             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.23/8.45      inference('sup-', [status(thm)], ['33', '36'])).
% 8.23/8.45  thf('38', plain,
% 8.23/8.45      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 8.23/8.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.45      inference('sup-', [status(thm)], ['6', '7'])).
% 8.23/8.45  thf(dt_k2_pre_topc, axiom,
% 8.23/8.45    (![A:$i,B:$i]:
% 8.23/8.45     ( ( ( l1_pre_topc @ A ) & 
% 8.23/8.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.23/8.45       ( m1_subset_1 @
% 8.23/8.45         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 8.23/8.45  thf('39', plain,
% 8.23/8.45      (![X14 : $i, X15 : $i]:
% 8.23/8.45         (~ (l1_pre_topc @ X14)
% 8.23/8.45          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 8.23/8.45          | (m1_subset_1 @ (k2_pre_topc @ X14 @ X15) @ 
% 8.23/8.45             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 8.23/8.45      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 8.23/8.45  thf('40', plain,
% 8.23/8.45      (((m1_subset_1 @ 
% 8.23/8.45         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 8.23/8.45         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.23/8.45        | ~ (l1_pre_topc @ sk_A))),
% 8.23/8.45      inference('sup-', [status(thm)], ['38', '39'])).
% 8.23/8.45  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 8.23/8.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.23/8.45  thf('42', plain,
% 8.23/8.45      ((m1_subset_1 @ 
% 8.23/8.45        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 8.23/8.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.45      inference('demod', [status(thm)], ['40', '41'])).
% 8.23/8.45  thf('43', plain,
% 8.23/8.45      (![X3 : $i, X4 : $i]:
% 8.23/8.45         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 8.23/8.45          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 8.23/8.45      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 8.23/8.45  thf('44', plain,
% 8.23/8.45      ((m1_subset_1 @ 
% 8.23/8.45        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.45         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 8.23/8.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.45      inference('sup-', [status(thm)], ['42', '43'])).
% 8.23/8.45  thf('45', plain,
% 8.23/8.45      (((k1_tops_1 @ sk_A @ sk_B)
% 8.23/8.45         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.23/8.45            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 8.23/8.45      inference('demod', [status(thm)], ['30', '31'])).
% 8.23/8.45  thf('46', plain,
% 8.23/8.45      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.23/8.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.23/8.45      inference('demod', [status(thm)], ['44', '45'])).
% 8.23/8.45  thf('47', plain,
% 8.23/8.45      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 8.23/8.45      inference('demod', [status(thm)], ['37', '46'])).
% 8.23/8.45  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 8.23/8.45  
% 8.23/8.45  % SZS output end Refutation
% 8.23/8.45  
% 8.23/8.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
