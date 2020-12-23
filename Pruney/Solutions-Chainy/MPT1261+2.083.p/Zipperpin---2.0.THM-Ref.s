%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fJeZ2d8ERp

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:50 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 189 expanded)
%              Number of leaves         :   32 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          : 1089 (2445 expanded)
%              Number of equality atoms :   87 ( 164 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v4_pre_topc @ X20 @ X21 )
      | ( ( k2_pre_topc @ X21 @ X20 )
        = X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k2_tops_1 @ X25 @ X24 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k2_pre_topc @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('32',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X10 @ X11 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X10 @ X11 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('40',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k2_pre_topc @ X27 @ X26 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ ( k2_tops_1 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('44',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42','51'])).

thf('53',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','52'])).

thf('54',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('55',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('65',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['53','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_pre_topc @ X21 )
      | ( ( k2_pre_topc @ X21 @ X20 )
       != X20 )
      | ( v4_pre_topc @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fJeZ2d8ERp
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:00:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 140 iterations in 0.088s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.37/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.37/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.37/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.55  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.37/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(t77_tops_1, conjecture,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55           ( ( v4_pre_topc @ B @ A ) <=>
% 0.37/0.55             ( ( k2_tops_1 @ A @ B ) =
% 0.37/0.55               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i]:
% 0.37/0.55        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.55          ( ![B:$i]:
% 0.37/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55              ( ( v4_pre_topc @ B @ A ) <=>
% 0.37/0.55                ( ( k2_tops_1 @ A @ B ) =
% 0.37/0.55                  ( k7_subset_1 @
% 0.37/0.55                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55              (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (~
% 0.37/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.37/0.55       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55             (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.55        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.55      inference('split', [status(esa)], ['2'])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t52_pre_topc, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_pre_topc @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.37/0.55             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.37/0.55               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.37/0.55          | ~ (v4_pre_topc @ X20 @ X21)
% 0.37/0.55          | ((k2_pre_topc @ X21 @ X20) = (X20))
% 0.37/0.55          | ~ (l1_pre_topc @ X21))),
% 0.37/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.37/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.55  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.37/0.55         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['3', '8'])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(l78_tops_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_pre_topc @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55           ( ( k2_tops_1 @ A @ B ) =
% 0.37/0.55             ( k7_subset_1 @
% 0.37/0.55               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.37/0.55               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X24 : $i, X25 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.37/0.55          | ((k2_tops_1 @ X25 @ X24)
% 0.37/0.55              = (k7_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.37/0.55                 (k2_pre_topc @ X25 @ X24) @ (k1_tops_1 @ X25 @ X24)))
% 0.37/0.55          | ~ (l1_pre_topc @ X25))),
% 0.37/0.55      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.55               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.55  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.37/0.55            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55             (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.55         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['9', '14'])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(redefinition_k7_subset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.37/0.55          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.37/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.55         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['15', '18'])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.37/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55              (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.37/0.55             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['19', '22'])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.37/0.55       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.37/0.55       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.55      inference('split', [status(esa)], ['2'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.37/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55             (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.55      inference('split', [status(esa)], ['2'])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf(t48_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X4 : $i, X5 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.37/0.55           = (k3_xboole_0 @ X4 @ X5))),
% 0.37/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.55          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf(t39_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (![X2 : $i, X3 : $i]:
% 0.37/0.55         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.37/0.55           = (k2_xboole_0 @ X2 @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.37/0.55          (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.55          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.37/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['30', '31'])).
% 0.37/0.55  thf(commutativity_k2_tarski, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.37/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.55  thf(l51_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i]:
% 0.37/0.55         ((k3_tarski @ (k2_tarski @ X10 @ X11)) = (k2_xboole_0 @ X10 @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['33', '34'])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i]:
% 0.37/0.55         ((k3_tarski @ (k2_tarski @ X10 @ X11)) = (k2_xboole_0 @ X10 @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.37/0.55          (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.55          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.37/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.55      inference('demod', [status(thm)], ['32', '37'])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t65_tops_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( l1_pre_topc @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.55           ( ( k2_pre_topc @ A @ B ) =
% 0.37/0.55             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X26 : $i, X27 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.37/0.55          | ((k2_pre_topc @ X27 @ X26)
% 0.37/0.55              = (k4_subset_1 @ (u1_struct_0 @ X27) @ X26 @ 
% 0.37/0.55                 (k2_tops_1 @ X27 @ X26)))
% 0.37/0.55          | ~ (l1_pre_topc @ X27))),
% 0.37/0.55      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.37/0.55            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(dt_k2_tops_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.55       ( m1_subset_1 @
% 0.37/0.55         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (![X22 : $i, X23 : $i]:
% 0.37/0.55         (~ (l1_pre_topc @ X22)
% 0.37/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.37/0.55          | (m1_subset_1 @ (k2_tops_1 @ X22 @ X23) @ 
% 0.37/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.37/0.55  thf('45', plain,
% 0.37/0.55      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.37/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.55  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.37/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.55  thf('48', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(redefinition_k4_subset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.37/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.55       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.37/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 0.37/0.55          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.37/0.55  thf('50', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.37/0.55            = (k2_xboole_0 @ sk_B @ X0))
% 0.37/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.55         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['47', '50'])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      (((k2_pre_topc @ sk_A @ sk_B)
% 0.37/0.55         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.55      inference('demod', [status(thm)], ['41', '42', '51'])).
% 0.37/0.55  thf('53', plain,
% 0.37/0.55      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.37/0.55          (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.55          = (k2_pre_topc @ sk_A @ sk_B)))
% 0.37/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.55      inference('demod', [status(thm)], ['38', '52'])).
% 0.37/0.55  thf('54', plain,
% 0.37/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf('55', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.37/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.55  thf(t12_setfam_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('56', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i]:
% 0.37/0.55         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.37/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.55  thf('57', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['55', '56'])).
% 0.37/0.55  thf('58', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i]:
% 0.37/0.55         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.37/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.55  thf('59', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['57', '58'])).
% 0.37/0.55  thf(t51_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.37/0.55       ( A ) ))).
% 0.37/0.55  thf('60', plain,
% 0.37/0.55      (![X6 : $i, X7 : $i]:
% 0.37/0.55         ((k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X7))
% 0.37/0.55           = (X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.37/0.55  thf('61', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.37/0.55           = (X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['59', '60'])).
% 0.37/0.55  thf('62', plain,
% 0.37/0.55      ((((k2_xboole_0 @ (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.37/0.55          (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.37/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['54', '61'])).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['57', '58'])).
% 0.37/0.55  thf('64', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.55  thf('65', plain,
% 0.37/0.55      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.37/0.55          (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.37/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.55      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.37/0.55  thf('66', plain,
% 0.37/0.55      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.37/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['53', '65'])).
% 0.37/0.55  thf('67', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('68', plain,
% 0.37/0.55      (![X20 : $i, X21 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.37/0.55          | ~ (v2_pre_topc @ X21)
% 0.37/0.55          | ((k2_pre_topc @ X21 @ X20) != (X20))
% 0.37/0.55          | (v4_pre_topc @ X20 @ X21)
% 0.37/0.55          | ~ (l1_pre_topc @ X21))),
% 0.37/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.37/0.55  thf('69', plain,
% 0.37/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.55        | (v4_pre_topc @ sk_B @ sk_A)
% 0.37/0.55        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.37/0.55        | ~ (v2_pre_topc @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['67', '68'])).
% 0.37/0.55  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('72', plain,
% 0.37/0.55      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.37/0.55      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.37/0.55  thf('73', plain,
% 0.37/0.55      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.37/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['66', '72'])).
% 0.37/0.55  thf('74', plain,
% 0.37/0.55      (((v4_pre_topc @ sk_B @ sk_A))
% 0.37/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['73'])).
% 0.37/0.55  thf('75', plain,
% 0.37/0.55      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('76', plain,
% 0.37/0.55      (~
% 0.37/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.55             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.37/0.55       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['74', '75'])).
% 0.37/0.55  thf('77', plain, ($false),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '76'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
