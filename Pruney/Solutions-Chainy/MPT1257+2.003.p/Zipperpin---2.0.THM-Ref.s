%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TIRR4sy4cL

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:18 EST 2020

% Result     : Theorem 9.82s
% Output     : Refutation 9.82s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 143 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  788 (1548 expanded)
%              Number of equality atoms :   22 (  23 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X11 @ ( k4_subset_1 @ X11 @ X12 @ X10 ) ) @ ( k3_subset_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k2_pre_topc @ X25 @ X24 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 @ ( k2_tops_1 @ X25 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k2_tops_1 @ X23 @ X22 )
        = ( k2_tops_1 @ X23 @ ( k3_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('27',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','27'])).

thf('29',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','28'])).

thf('30',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k1_tops_1 @ X17 @ X16 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k2_pre_topc @ X17 @ ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','30','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('39',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t44_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ( r1_xboole_0 @ X15 @ ( k3_subset_1 @ X14 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t44_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('44',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TIRR4sy4cL
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:07:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 9.82/10.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.82/10.08  % Solved by: fo/fo7.sh
% 9.82/10.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.82/10.08  % done 2179 iterations in 9.634s
% 9.82/10.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.82/10.08  % SZS output start Refutation
% 9.82/10.08  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 9.82/10.08  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 9.82/10.08  thf(sk_A_type, type, sk_A: $i).
% 9.82/10.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.82/10.08  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 9.82/10.08  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 9.82/10.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.82/10.08  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 9.82/10.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 9.82/10.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.82/10.08  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 9.82/10.08  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 9.82/10.08  thf(sk_B_type, type, sk_B: $i).
% 9.82/10.08  thf(t73_tops_1, conjecture,
% 9.82/10.08    (![A:$i]:
% 9.82/10.08     ( ( l1_pre_topc @ A ) =>
% 9.82/10.08       ( ![B:$i]:
% 9.82/10.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.82/10.08           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 9.82/10.08  thf(zf_stmt_0, negated_conjecture,
% 9.82/10.08    (~( ![A:$i]:
% 9.82/10.08        ( ( l1_pre_topc @ A ) =>
% 9.82/10.08          ( ![B:$i]:
% 9.82/10.08            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.82/10.08              ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ) )),
% 9.82/10.08    inference('cnf.neg', [status(esa)], [t73_tops_1])).
% 9.82/10.08  thf('0', plain,
% 9.82/10.08      (~ (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 9.82/10.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.82/10.08  thf('1', plain,
% 9.82/10.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.82/10.08  thf(dt_k2_tops_1, axiom,
% 9.82/10.08    (![A:$i,B:$i]:
% 9.82/10.08     ( ( ( l1_pre_topc @ A ) & 
% 9.82/10.08         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 9.82/10.08       ( m1_subset_1 @
% 9.82/10.08         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 9.82/10.08  thf('2', plain,
% 9.82/10.08      (![X20 : $i, X21 : $i]:
% 9.82/10.08         (~ (l1_pre_topc @ X20)
% 9.82/10.08          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 9.82/10.08          | (m1_subset_1 @ (k2_tops_1 @ X20 @ X21) @ 
% 9.82/10.08             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 9.82/10.08      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 9.82/10.08  thf('3', plain,
% 9.82/10.08      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.82/10.08         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.82/10.08        | ~ (l1_pre_topc @ sk_A))),
% 9.82/10.08      inference('sup-', [status(thm)], ['1', '2'])).
% 9.82/10.08  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 9.82/10.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.82/10.08  thf('5', plain,
% 9.82/10.08      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.82/10.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('demod', [status(thm)], ['3', '4'])).
% 9.82/10.08  thf('6', plain,
% 9.82/10.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.82/10.08  thf(dt_k3_subset_1, axiom,
% 9.82/10.08    (![A:$i,B:$i]:
% 9.82/10.08     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.82/10.08       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.82/10.08  thf('7', plain,
% 9.82/10.08      (![X3 : $i, X4 : $i]:
% 9.82/10.08         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 9.82/10.08          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 9.82/10.08      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 9.82/10.08  thf('8', plain,
% 9.82/10.08      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 9.82/10.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('sup-', [status(thm)], ['6', '7'])).
% 9.82/10.08  thf(t41_subset_1, axiom,
% 9.82/10.08    (![A:$i,B:$i]:
% 9.82/10.08     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.82/10.08       ( ![C:$i]:
% 9.82/10.08         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.82/10.08           ( r1_tarski @
% 9.82/10.08             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 9.82/10.08             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 9.82/10.08  thf('9', plain,
% 9.82/10.08      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.82/10.08         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 9.82/10.08          | (r1_tarski @ 
% 9.82/10.08             (k3_subset_1 @ X11 @ (k4_subset_1 @ X11 @ X12 @ X10)) @ 
% 9.82/10.08             (k3_subset_1 @ X11 @ X12))
% 9.82/10.08          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 9.82/10.08      inference('cnf', [status(esa)], [t41_subset_1])).
% 9.82/10.08  thf('10', plain,
% 9.82/10.08      (![X0 : $i]:
% 9.82/10.08         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.82/10.08          | (r1_tarski @ 
% 9.82/10.08             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.82/10.08              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 9.82/10.08               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 9.82/10.08             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 9.82/10.08      inference('sup-', [status(thm)], ['8', '9'])).
% 9.82/10.08  thf('11', plain,
% 9.82/10.08      ((r1_tarski @ 
% 9.82/10.08        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.82/10.08         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.82/10.08          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 9.82/10.08        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 9.82/10.08      inference('sup-', [status(thm)], ['5', '10'])).
% 9.82/10.08  thf('12', plain,
% 9.82/10.08      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.82/10.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('demod', [status(thm)], ['3', '4'])).
% 9.82/10.08  thf('13', plain,
% 9.82/10.08      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 9.82/10.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('sup-', [status(thm)], ['6', '7'])).
% 9.82/10.08  thf(commutativity_k4_subset_1, axiom,
% 9.82/10.08    (![A:$i,B:$i,C:$i]:
% 9.82/10.08     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 9.82/10.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 9.82/10.08       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 9.82/10.08  thf('14', plain,
% 9.82/10.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.82/10.08         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 9.82/10.08          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1))
% 9.82/10.08          | ((k4_subset_1 @ X1 @ X0 @ X2) = (k4_subset_1 @ X1 @ X2 @ X0)))),
% 9.82/10.08      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 9.82/10.08  thf('15', plain,
% 9.82/10.08      (![X0 : $i]:
% 9.82/10.08         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.82/10.08            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 9.82/10.08            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 9.82/10.08               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 9.82/10.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 9.82/10.08      inference('sup-', [status(thm)], ['13', '14'])).
% 9.82/10.08  thf('16', plain,
% 9.82/10.08      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.82/10.08         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 9.82/10.08         (k2_tops_1 @ sk_A @ sk_B))
% 9.82/10.08         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.82/10.08            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 9.82/10.08      inference('sup-', [status(thm)], ['12', '15'])).
% 9.82/10.08  thf('17', plain,
% 9.82/10.08      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 9.82/10.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('sup-', [status(thm)], ['6', '7'])).
% 9.82/10.08  thf(t65_tops_1, axiom,
% 9.82/10.08    (![A:$i]:
% 9.82/10.08     ( ( l1_pre_topc @ A ) =>
% 9.82/10.08       ( ![B:$i]:
% 9.82/10.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.82/10.08           ( ( k2_pre_topc @ A @ B ) =
% 9.82/10.08             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 9.82/10.08  thf('18', plain,
% 9.82/10.08      (![X24 : $i, X25 : $i]:
% 9.82/10.08         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 9.82/10.08          | ((k2_pre_topc @ X25 @ X24)
% 9.82/10.08              = (k4_subset_1 @ (u1_struct_0 @ X25) @ X24 @ 
% 9.82/10.08                 (k2_tops_1 @ X25 @ X24)))
% 9.82/10.08          | ~ (l1_pre_topc @ X25))),
% 9.82/10.08      inference('cnf', [status(esa)], [t65_tops_1])).
% 9.82/10.08  thf('19', plain,
% 9.82/10.08      ((~ (l1_pre_topc @ sk_A)
% 9.82/10.08        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 9.82/10.08            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.82/10.08               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 9.82/10.08               (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 9.82/10.08      inference('sup-', [status(thm)], ['17', '18'])).
% 9.82/10.08  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 9.82/10.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.82/10.08  thf('21', plain,
% 9.82/10.08      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 9.82/10.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('sup-', [status(thm)], ['6', '7'])).
% 9.82/10.08  thf(t62_tops_1, axiom,
% 9.82/10.08    (![A:$i]:
% 9.82/10.08     ( ( l1_pre_topc @ A ) =>
% 9.82/10.08       ( ![B:$i]:
% 9.82/10.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.82/10.08           ( ( k2_tops_1 @ A @ B ) =
% 9.82/10.08             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 9.82/10.08  thf('22', plain,
% 9.82/10.08      (![X22 : $i, X23 : $i]:
% 9.82/10.08         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 9.82/10.08          | ((k2_tops_1 @ X23 @ X22)
% 9.82/10.08              = (k2_tops_1 @ X23 @ (k3_subset_1 @ (u1_struct_0 @ X23) @ X22)))
% 9.82/10.08          | ~ (l1_pre_topc @ X23))),
% 9.82/10.08      inference('cnf', [status(esa)], [t62_tops_1])).
% 9.82/10.08  thf('23', plain,
% 9.82/10.08      ((~ (l1_pre_topc @ sk_A)
% 9.82/10.08        | ((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 9.82/10.08            = (k2_tops_1 @ sk_A @ 
% 9.82/10.08               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.82/10.08                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 9.82/10.08      inference('sup-', [status(thm)], ['21', '22'])).
% 9.82/10.08  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 9.82/10.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.82/10.08  thf('25', plain,
% 9.82/10.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.82/10.08  thf(involutiveness_k3_subset_1, axiom,
% 9.82/10.08    (![A:$i,B:$i]:
% 9.82/10.08     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.82/10.08       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 9.82/10.08  thf('26', plain,
% 9.82/10.08      (![X5 : $i, X6 : $i]:
% 9.82/10.08         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 9.82/10.08          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 9.82/10.08      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 9.82/10.08  thf('27', plain,
% 9.82/10.08      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.82/10.08         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 9.82/10.08      inference('sup-', [status(thm)], ['25', '26'])).
% 9.82/10.08  thf('28', plain,
% 9.82/10.08      (((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 9.82/10.08         = (k2_tops_1 @ sk_A @ sk_B))),
% 9.82/10.08      inference('demod', [status(thm)], ['23', '24', '27'])).
% 9.82/10.08  thf('29', plain,
% 9.82/10.08      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 9.82/10.08         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.82/10.08            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 9.82/10.08            (k2_tops_1 @ sk_A @ sk_B)))),
% 9.82/10.08      inference('demod', [status(thm)], ['19', '20', '28'])).
% 9.82/10.08  thf('30', plain,
% 9.82/10.08      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 9.82/10.08         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.82/10.08            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 9.82/10.08      inference('sup+', [status(thm)], ['16', '29'])).
% 9.82/10.08  thf('31', plain,
% 9.82/10.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.82/10.08  thf(d1_tops_1, axiom,
% 9.82/10.08    (![A:$i]:
% 9.82/10.08     ( ( l1_pre_topc @ A ) =>
% 9.82/10.08       ( ![B:$i]:
% 9.82/10.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.82/10.08           ( ( k1_tops_1 @ A @ B ) =
% 9.82/10.08             ( k3_subset_1 @
% 9.82/10.08               ( u1_struct_0 @ A ) @ 
% 9.82/10.08               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 9.82/10.08  thf('32', plain,
% 9.82/10.08      (![X16 : $i, X17 : $i]:
% 9.82/10.08         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 9.82/10.08          | ((k1_tops_1 @ X17 @ X16)
% 9.82/10.08              = (k3_subset_1 @ (u1_struct_0 @ X17) @ 
% 9.82/10.08                 (k2_pre_topc @ X17 @ (k3_subset_1 @ (u1_struct_0 @ X17) @ X16))))
% 9.82/10.08          | ~ (l1_pre_topc @ X17))),
% 9.82/10.08      inference('cnf', [status(esa)], [d1_tops_1])).
% 9.82/10.08  thf('33', plain,
% 9.82/10.08      ((~ (l1_pre_topc @ sk_A)
% 9.82/10.08        | ((k1_tops_1 @ sk_A @ sk_B)
% 9.82/10.08            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.82/10.08               (k2_pre_topc @ sk_A @ 
% 9.82/10.08                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 9.82/10.08      inference('sup-', [status(thm)], ['31', '32'])).
% 9.82/10.08  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 9.82/10.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.82/10.08  thf('35', plain,
% 9.82/10.08      (((k1_tops_1 @ sk_A @ sk_B)
% 9.82/10.08         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.82/10.08            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 9.82/10.08      inference('demod', [status(thm)], ['33', '34'])).
% 9.82/10.08  thf('36', plain,
% 9.82/10.08      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 9.82/10.08        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 9.82/10.08      inference('demod', [status(thm)], ['11', '30', '35'])).
% 9.82/10.08  thf('37', plain,
% 9.82/10.08      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.82/10.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('demod', [status(thm)], ['3', '4'])).
% 9.82/10.08  thf('38', plain,
% 9.82/10.08      (![X3 : $i, X4 : $i]:
% 9.82/10.08         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 9.82/10.08          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 9.82/10.08      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 9.82/10.08  thf('39', plain,
% 9.82/10.08      ((m1_subset_1 @ 
% 9.82/10.08        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 9.82/10.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('sup-', [status(thm)], ['37', '38'])).
% 9.82/10.08  thf(t44_subset_1, axiom,
% 9.82/10.08    (![A:$i,B:$i]:
% 9.82/10.08     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.82/10.08       ( ![C:$i]:
% 9.82/10.08         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.82/10.08           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 9.82/10.08             ( r1_tarski @ B @ C ) ) ) ) ))).
% 9.82/10.08  thf('40', plain,
% 9.82/10.08      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.82/10.08         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 9.82/10.08          | ~ (r1_tarski @ X15 @ X13)
% 9.82/10.08          | (r1_xboole_0 @ X15 @ (k3_subset_1 @ X14 @ X13))
% 9.82/10.08          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 9.82/10.08      inference('cnf', [status(esa)], [t44_subset_1])).
% 9.82/10.08  thf('41', plain,
% 9.82/10.08      (![X0 : $i]:
% 9.82/10.08         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.82/10.08          | (r1_xboole_0 @ X0 @ 
% 9.82/10.08             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.82/10.08              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))
% 9.82/10.08          | ~ (r1_tarski @ X0 @ 
% 9.82/10.08               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 9.82/10.08      inference('sup-', [status(thm)], ['39', '40'])).
% 9.82/10.08  thf('42', plain,
% 9.82/10.08      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.82/10.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('demod', [status(thm)], ['3', '4'])).
% 9.82/10.08  thf('43', plain,
% 9.82/10.08      (![X5 : $i, X6 : $i]:
% 9.82/10.08         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 9.82/10.08          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 9.82/10.08      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 9.82/10.08  thf('44', plain,
% 9.82/10.08      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.82/10.08         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))
% 9.82/10.08         = (k2_tops_1 @ sk_A @ sk_B))),
% 9.82/10.08      inference('sup-', [status(thm)], ['42', '43'])).
% 9.82/10.08  thf('45', plain,
% 9.82/10.08      (![X0 : $i]:
% 9.82/10.08         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.82/10.08          | (r1_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 9.82/10.08          | ~ (r1_tarski @ X0 @ 
% 9.82/10.08               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 9.82/10.08      inference('demod', [status(thm)], ['41', '44'])).
% 9.82/10.08  thf('46', plain,
% 9.82/10.08      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 9.82/10.08        | ~ (m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 9.82/10.08             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 9.82/10.08      inference('sup-', [status(thm)], ['36', '45'])).
% 9.82/10.08  thf('47', plain,
% 9.82/10.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.82/10.08  thf(dt_k1_tops_1, axiom,
% 9.82/10.08    (![A:$i,B:$i]:
% 9.82/10.08     ( ( ( l1_pre_topc @ A ) & 
% 9.82/10.08         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 9.82/10.08       ( m1_subset_1 @
% 9.82/10.08         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 9.82/10.08  thf('48', plain,
% 9.82/10.08      (![X18 : $i, X19 : $i]:
% 9.82/10.08         (~ (l1_pre_topc @ X18)
% 9.82/10.08          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 9.82/10.08          | (m1_subset_1 @ (k1_tops_1 @ X18 @ X19) @ 
% 9.82/10.08             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 9.82/10.08      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 9.82/10.08  thf('49', plain,
% 9.82/10.08      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 9.82/10.08         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.82/10.08        | ~ (l1_pre_topc @ sk_A))),
% 9.82/10.08      inference('sup-', [status(thm)], ['47', '48'])).
% 9.82/10.08  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 9.82/10.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.82/10.08  thf('51', plain,
% 9.82/10.08      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 9.82/10.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.82/10.08      inference('demod', [status(thm)], ['49', '50'])).
% 9.82/10.08  thf('52', plain,
% 9.82/10.08      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 9.82/10.08      inference('demod', [status(thm)], ['46', '51'])).
% 9.82/10.08  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 9.82/10.08  
% 9.82/10.08  % SZS output end Refutation
% 9.82/10.08  
% 9.82/10.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
