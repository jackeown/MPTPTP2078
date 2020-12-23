%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XYx7LCpSM6

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:43 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 319 expanded)
%              Number of leaves         :   37 ( 105 expanded)
%              Depth                    :   15
%              Number of atoms          : 1267 (4121 expanded)
%              Number of equality atoms :   87 ( 231 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v4_pre_topc @ X26 @ X27 )
      | ( ( k2_pre_topc @ X27 @ X26 )
        = X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k2_tops_1 @ X33 @ X32 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X33 ) @ ( k2_pre_topc @ X33 @ X32 ) @ ( k1_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('34',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X35 @ X34 ) @ X34 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('51',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('53',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_subset_1 @ X19 @ X20 @ ( k3_subset_1 @ X19 @ X20 ) )
        = ( k2_subset_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('56',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('57',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_subset_1 @ X19 @ X20 @ ( k3_subset_1 @ X19 @ X20 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','59'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('61',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('62',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('65',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('74',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k2_pre_topc @ X37 @ X36 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 @ ( k2_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63','78'])).

thf('80',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','59'])).

thf('81',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('83',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X30 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('84',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['81','87'])).

thf('89',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XYx7LCpSM6
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:46:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.19/1.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.19/1.39  % Solved by: fo/fo7.sh
% 1.19/1.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.39  % done 988 iterations in 0.932s
% 1.19/1.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.19/1.39  % SZS output start Refutation
% 1.19/1.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.19/1.39  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.19/1.39  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.19/1.39  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.19/1.39  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.19/1.39  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.19/1.39  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.19/1.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.39  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.19/1.39  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.19/1.39  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.19/1.39  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.19/1.39  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.39  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.19/1.39  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.19/1.39  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.19/1.39  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.19/1.39  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.19/1.39  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.19/1.39  thf(t77_tops_1, conjecture,
% 1.19/1.39    (![A:$i]:
% 1.19/1.39     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.39       ( ![B:$i]:
% 1.19/1.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.39           ( ( v4_pre_topc @ B @ A ) <=>
% 1.19/1.39             ( ( k2_tops_1 @ A @ B ) =
% 1.19/1.39               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.19/1.39  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.39    (~( ![A:$i]:
% 1.19/1.39        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.39          ( ![B:$i]:
% 1.19/1.39            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.39              ( ( v4_pre_topc @ B @ A ) <=>
% 1.19/1.39                ( ( k2_tops_1 @ A @ B ) =
% 1.19/1.39                  ( k7_subset_1 @
% 1.19/1.39                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.19/1.39    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.19/1.39  thf('0', plain,
% 1.19/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39              (k1_tops_1 @ sk_A @ sk_B)))
% 1.19/1.39        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('1', plain,
% 1.19/1.39      (~
% 1.19/1.39       (((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.19/1.39       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.39      inference('split', [status(esa)], ['0'])).
% 1.19/1.39  thf('2', plain,
% 1.19/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39             (k1_tops_1 @ sk_A @ sk_B)))
% 1.19/1.39        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('3', plain,
% 1.19/1.39      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.19/1.39      inference('split', [status(esa)], ['2'])).
% 1.19/1.39  thf('4', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(t52_pre_topc, axiom,
% 1.19/1.39    (![A:$i]:
% 1.19/1.39     ( ( l1_pre_topc @ A ) =>
% 1.19/1.39       ( ![B:$i]:
% 1.19/1.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.39           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.19/1.39             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.19/1.39               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.19/1.39  thf('5', plain,
% 1.19/1.39      (![X26 : $i, X27 : $i]:
% 1.19/1.39         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.19/1.39          | ~ (v4_pre_topc @ X26 @ X27)
% 1.19/1.39          | ((k2_pre_topc @ X27 @ X26) = (X26))
% 1.19/1.39          | ~ (l1_pre_topc @ X27))),
% 1.19/1.39      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.19/1.39  thf('6', plain,
% 1.19/1.39      ((~ (l1_pre_topc @ sk_A)
% 1.19/1.39        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 1.19/1.39        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.39      inference('sup-', [status(thm)], ['4', '5'])).
% 1.19/1.39  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('8', plain,
% 1.19/1.39      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.39      inference('demod', [status(thm)], ['6', '7'])).
% 1.19/1.39  thf('9', plain,
% 1.19/1.39      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.19/1.39         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['3', '8'])).
% 1.19/1.39  thf('10', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(l78_tops_1, axiom,
% 1.19/1.39    (![A:$i]:
% 1.19/1.39     ( ( l1_pre_topc @ A ) =>
% 1.19/1.39       ( ![B:$i]:
% 1.19/1.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.39           ( ( k2_tops_1 @ A @ B ) =
% 1.19/1.39             ( k7_subset_1 @
% 1.19/1.39               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.19/1.39               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.19/1.39  thf('11', plain,
% 1.19/1.39      (![X32 : $i, X33 : $i]:
% 1.19/1.39         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.19/1.39          | ((k2_tops_1 @ X33 @ X32)
% 1.19/1.39              = (k7_subset_1 @ (u1_struct_0 @ X33) @ 
% 1.19/1.39                 (k2_pre_topc @ X33 @ X32) @ (k1_tops_1 @ X33 @ X32)))
% 1.19/1.39          | ~ (l1_pre_topc @ X33))),
% 1.19/1.39      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.19/1.39  thf('12', plain,
% 1.19/1.39      ((~ (l1_pre_topc @ sk_A)
% 1.19/1.39        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.39               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.19/1.39      inference('sup-', [status(thm)], ['10', '11'])).
% 1.19/1.39  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('14', plain,
% 1.19/1.39      (((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.19/1.39            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.19/1.39      inference('demod', [status(thm)], ['12', '13'])).
% 1.19/1.39  thf('15', plain,
% 1.19/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39             (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.39         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.19/1.39      inference('sup+', [status(thm)], ['9', '14'])).
% 1.19/1.39  thf('16', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(redefinition_k7_subset_1, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i]:
% 1.19/1.39     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.19/1.39       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.19/1.39  thf('17', plain,
% 1.19/1.39      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.19/1.39         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.19/1.39          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 1.19/1.39      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.19/1.39  thf('18', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.19/1.39           = (k4_xboole_0 @ sk_B @ X0))),
% 1.19/1.39      inference('sup-', [status(thm)], ['16', '17'])).
% 1.19/1.39  thf('19', plain,
% 1.19/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.39         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.19/1.39      inference('demod', [status(thm)], ['15', '18'])).
% 1.19/1.39  thf('20', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.19/1.39           = (k4_xboole_0 @ sk_B @ X0))),
% 1.19/1.39      inference('sup-', [status(thm)], ['16', '17'])).
% 1.19/1.39  thf('21', plain,
% 1.19/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39              (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.39         <= (~
% 1.19/1.39             (((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('split', [status(esa)], ['0'])).
% 1.19/1.39  thf('22', plain,
% 1.19/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.39         <= (~
% 1.19/1.39             (((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup-', [status(thm)], ['20', '21'])).
% 1.19/1.39  thf('23', plain,
% 1.19/1.39      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.19/1.39         <= (~
% 1.19/1.39             (((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.19/1.39             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['19', '22'])).
% 1.19/1.39  thf('24', plain,
% 1.19/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.19/1.39       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.39      inference('simplify', [status(thm)], ['23'])).
% 1.19/1.39  thf('25', plain,
% 1.19/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.19/1.39       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.39      inference('split', [status(esa)], ['2'])).
% 1.19/1.39  thf('26', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.19/1.39           = (k4_xboole_0 @ sk_B @ X0))),
% 1.19/1.39      inference('sup-', [status(thm)], ['16', '17'])).
% 1.19/1.39  thf('27', plain,
% 1.19/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39             (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('split', [status(esa)], ['2'])).
% 1.19/1.39  thf('28', plain,
% 1.19/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup+', [status(thm)], ['26', '27'])).
% 1.19/1.39  thf(t36_xboole_1, axiom,
% 1.19/1.39    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.19/1.39  thf('29', plain,
% 1.19/1.39      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 1.19/1.39      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.19/1.39  thf(t3_subset, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.19/1.39  thf('30', plain,
% 1.19/1.39      (![X23 : $i, X25 : $i]:
% 1.19/1.39         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 1.19/1.39      inference('cnf', [status(esa)], [t3_subset])).
% 1.19/1.39  thf('31', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.19/1.39      inference('sup-', [status(thm)], ['29', '30'])).
% 1.19/1.39  thf('32', plain,
% 1.19/1.39      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup+', [status(thm)], ['28', '31'])).
% 1.19/1.39  thf('33', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(t44_tops_1, axiom,
% 1.19/1.39    (![A:$i]:
% 1.19/1.39     ( ( l1_pre_topc @ A ) =>
% 1.19/1.39       ( ![B:$i]:
% 1.19/1.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.39           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.19/1.39  thf('34', plain,
% 1.19/1.39      (![X34 : $i, X35 : $i]:
% 1.19/1.39         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 1.19/1.39          | (r1_tarski @ (k1_tops_1 @ X35 @ X34) @ X34)
% 1.19/1.39          | ~ (l1_pre_topc @ X35))),
% 1.19/1.39      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.19/1.39  thf('35', plain,
% 1.19/1.39      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.19/1.39      inference('sup-', [status(thm)], ['33', '34'])).
% 1.19/1.39  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('37', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.19/1.39      inference('demod', [status(thm)], ['35', '36'])).
% 1.19/1.39  thf('38', plain,
% 1.19/1.39      (![X23 : $i, X25 : $i]:
% 1.19/1.39         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 1.19/1.39      inference('cnf', [status(esa)], [t3_subset])).
% 1.19/1.39  thf('39', plain,
% 1.19/1.39      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 1.19/1.39      inference('sup-', [status(thm)], ['37', '38'])).
% 1.19/1.39  thf(redefinition_k4_subset_1, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i]:
% 1.19/1.39     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.19/1.39         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.19/1.39       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.19/1.39  thf('40', plain,
% 1.19/1.39      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.19/1.39         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.19/1.39          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 1.19/1.39          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 1.19/1.39      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.19/1.39  thf('41', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.19/1.39            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 1.19/1.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['39', '40'])).
% 1.19/1.39  thf('42', plain,
% 1.19/1.39      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.19/1.39          (k2_tops_1 @ sk_A @ sk_B))
% 1.19/1.39          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.19/1.39             (k2_tops_1 @ sk_A @ sk_B))))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup-', [status(thm)], ['32', '41'])).
% 1.19/1.39  thf(commutativity_k2_tarski, axiom,
% 1.19/1.39    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.19/1.39  thf('43', plain,
% 1.19/1.39      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 1.19/1.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.19/1.39  thf(l51_zfmisc_1, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.19/1.39  thf('44', plain,
% 1.19/1.39      (![X8 : $i, X9 : $i]:
% 1.19/1.39         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 1.19/1.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.19/1.39  thf('45', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]:
% 1.19/1.39         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.19/1.39      inference('sup+', [status(thm)], ['43', '44'])).
% 1.19/1.39  thf('46', plain,
% 1.19/1.39      (![X8 : $i, X9 : $i]:
% 1.19/1.39         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 1.19/1.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.19/1.39  thf('47', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.19/1.39      inference('sup+', [status(thm)], ['45', '46'])).
% 1.19/1.39  thf('48', plain,
% 1.19/1.39      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.19/1.39          (k2_tops_1 @ sk_A @ sk_B))
% 1.19/1.39          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.19/1.39             (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('demod', [status(thm)], ['42', '47'])).
% 1.19/1.39  thf('49', plain,
% 1.19/1.39      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 1.19/1.39      inference('sup-', [status(thm)], ['37', '38'])).
% 1.19/1.39  thf(d5_subset_1, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.19/1.39       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.19/1.39  thf('50', plain,
% 1.19/1.39      (![X11 : $i, X12 : $i]:
% 1.19/1.39         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 1.19/1.39          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 1.19/1.39      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.19/1.39  thf('51', plain,
% 1.19/1.39      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.19/1.39         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['49', '50'])).
% 1.19/1.39  thf('52', plain,
% 1.19/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup+', [status(thm)], ['26', '27'])).
% 1.19/1.39  thf('53', plain,
% 1.19/1.39      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          = (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup+', [status(thm)], ['51', '52'])).
% 1.19/1.39  thf('54', plain,
% 1.19/1.39      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 1.19/1.39      inference('sup-', [status(thm)], ['37', '38'])).
% 1.19/1.39  thf(t25_subset_1, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.19/1.39       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.19/1.39         ( k2_subset_1 @ A ) ) ))).
% 1.19/1.39  thf('55', plain,
% 1.19/1.39      (![X19 : $i, X20 : $i]:
% 1.19/1.39         (((k4_subset_1 @ X19 @ X20 @ (k3_subset_1 @ X19 @ X20))
% 1.19/1.39            = (k2_subset_1 @ X19))
% 1.19/1.39          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 1.19/1.39      inference('cnf', [status(esa)], [t25_subset_1])).
% 1.19/1.39  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.19/1.39  thf('56', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 1.19/1.39      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.19/1.39  thf('57', plain,
% 1.19/1.39      (![X19 : $i, X20 : $i]:
% 1.19/1.39         (((k4_subset_1 @ X19 @ X20 @ (k3_subset_1 @ X19 @ X20)) = (X19))
% 1.19/1.39          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 1.19/1.39      inference('demod', [status(thm)], ['55', '56'])).
% 1.19/1.39  thf('58', plain,
% 1.19/1.39      (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.19/1.39         (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 1.19/1.39      inference('sup-', [status(thm)], ['54', '57'])).
% 1.19/1.39  thf('59', plain,
% 1.19/1.39      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.19/1.39          (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup+', [status(thm)], ['53', '58'])).
% 1.19/1.39  thf('60', plain,
% 1.19/1.39      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.19/1.39          = (sk_B)))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup+', [status(thm)], ['48', '59'])).
% 1.19/1.39  thf(t6_xboole_1, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.19/1.39  thf('61', plain,
% 1.19/1.39      (![X4 : $i, X5 : $i]:
% 1.19/1.39         ((k2_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5))
% 1.19/1.39           = (k2_xboole_0 @ X4 @ X5))),
% 1.19/1.39      inference('cnf', [status(esa)], [t6_xboole_1])).
% 1.19/1.39  thf('62', plain,
% 1.19/1.39      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.19/1.39          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.19/1.39             (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup+', [status(thm)], ['60', '61'])).
% 1.19/1.39  thf('63', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.19/1.39      inference('sup+', [status(thm)], ['45', '46'])).
% 1.19/1.39  thf('64', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(dt_k2_tops_1, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( ( l1_pre_topc @ A ) & 
% 1.19/1.39         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.19/1.39       ( m1_subset_1 @
% 1.19/1.39         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.19/1.39  thf('65', plain,
% 1.19/1.39      (![X28 : $i, X29 : $i]:
% 1.19/1.39         (~ (l1_pre_topc @ X28)
% 1.19/1.39          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.19/1.39          | (m1_subset_1 @ (k2_tops_1 @ X28 @ X29) @ 
% 1.19/1.39             (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 1.19/1.39      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.19/1.39  thf('66', plain,
% 1.19/1.39      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.19/1.39         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.19/1.39        | ~ (l1_pre_topc @ sk_A))),
% 1.19/1.39      inference('sup-', [status(thm)], ['64', '65'])).
% 1.19/1.39  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('68', plain,
% 1.19/1.39      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.19/1.39        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.39      inference('demod', [status(thm)], ['66', '67'])).
% 1.19/1.39  thf('69', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('70', plain,
% 1.19/1.39      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.19/1.39         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.19/1.39          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 1.19/1.39          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 1.19/1.39      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.19/1.39  thf('71', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.19/1.39            = (k2_xboole_0 @ sk_B @ X0))
% 1.19/1.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.19/1.39      inference('sup-', [status(thm)], ['69', '70'])).
% 1.19/1.39  thf('72', plain,
% 1.19/1.39      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.19/1.39         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['68', '71'])).
% 1.19/1.39  thf('73', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(t65_tops_1, axiom,
% 1.19/1.39    (![A:$i]:
% 1.19/1.39     ( ( l1_pre_topc @ A ) =>
% 1.19/1.39       ( ![B:$i]:
% 1.19/1.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.39           ( ( k2_pre_topc @ A @ B ) =
% 1.19/1.39             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.19/1.39  thf('74', plain,
% 1.19/1.39      (![X36 : $i, X37 : $i]:
% 1.19/1.39         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.19/1.39          | ((k2_pre_topc @ X37 @ X36)
% 1.19/1.39              = (k4_subset_1 @ (u1_struct_0 @ X37) @ X36 @ 
% 1.19/1.39                 (k2_tops_1 @ X37 @ X36)))
% 1.19/1.39          | ~ (l1_pre_topc @ X37))),
% 1.19/1.39      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.19/1.39  thf('75', plain,
% 1.19/1.39      ((~ (l1_pre_topc @ sk_A)
% 1.19/1.39        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.19/1.39            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.19/1.39      inference('sup-', [status(thm)], ['73', '74'])).
% 1.19/1.39  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('77', plain,
% 1.19/1.39      (((k2_pre_topc @ sk_A @ sk_B)
% 1.19/1.39         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.19/1.39      inference('demod', [status(thm)], ['75', '76'])).
% 1.19/1.39  thf('78', plain,
% 1.19/1.39      (((k2_pre_topc @ sk_A @ sk_B)
% 1.19/1.39         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.19/1.39      inference('sup+', [status(thm)], ['72', '77'])).
% 1.19/1.39  thf('79', plain,
% 1.19/1.39      ((((k2_pre_topc @ sk_A @ sk_B)
% 1.19/1.39          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.19/1.39             (k1_tops_1 @ sk_A @ sk_B))))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('demod', [status(thm)], ['62', '63', '78'])).
% 1.19/1.39  thf('80', plain,
% 1.19/1.39      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.19/1.39          = (sk_B)))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup+', [status(thm)], ['48', '59'])).
% 1.19/1.39  thf('81', plain,
% 1.19/1.39      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup+', [status(thm)], ['79', '80'])).
% 1.19/1.39  thf('82', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(fc1_tops_1, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.19/1.39         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.19/1.39       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.19/1.39  thf('83', plain,
% 1.19/1.39      (![X30 : $i, X31 : $i]:
% 1.19/1.39         (~ (l1_pre_topc @ X30)
% 1.19/1.39          | ~ (v2_pre_topc @ X30)
% 1.19/1.39          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.19/1.39          | (v4_pre_topc @ (k2_pre_topc @ X30 @ X31) @ X30))),
% 1.19/1.39      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.19/1.39  thf('84', plain,
% 1.19/1.39      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.19/1.39        | ~ (v2_pre_topc @ sk_A)
% 1.19/1.39        | ~ (l1_pre_topc @ sk_A))),
% 1.19/1.39      inference('sup-', [status(thm)], ['82', '83'])).
% 1.19/1.39  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('87', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.19/1.39      inference('demod', [status(thm)], ['84', '85', '86'])).
% 1.19/1.39  thf('88', plain,
% 1.19/1.39      (((v4_pre_topc @ sk_B @ sk_A))
% 1.19/1.39         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.19/1.39      inference('sup+', [status(thm)], ['81', '87'])).
% 1.19/1.39  thf('89', plain,
% 1.19/1.39      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.19/1.39      inference('split', [status(esa)], ['0'])).
% 1.19/1.39  thf('90', plain,
% 1.19/1.39      (~
% 1.19/1.39       (((k2_tops_1 @ sk_A @ sk_B)
% 1.19/1.39          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.19/1.39             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.19/1.39       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.19/1.39      inference('sup-', [status(thm)], ['88', '89'])).
% 1.19/1.39  thf('91', plain, ($false),
% 1.19/1.39      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '90'])).
% 1.19/1.39  
% 1.19/1.39  % SZS output end Refutation
% 1.19/1.39  
% 1.19/1.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
