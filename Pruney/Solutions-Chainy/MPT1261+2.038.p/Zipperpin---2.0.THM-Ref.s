%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BjqZPobMVZ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:43 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 387 expanded)
%              Number of leaves         :   37 ( 125 expanded)
%              Depth                    :   19
%              Number of atoms          : 1325 (4903 expanded)
%              Number of equality atoms :   88 ( 253 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('30',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X35 @ X34 ) @ X34 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['31','32'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('37',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','43'])).

thf('45',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ X7 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ X7 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('58',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_subset_1 @ X19 @ X20 @ ( k3_subset_1 @ X19 @ X20 ) )
        = ( k2_subset_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('60',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('61',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_subset_1 @ X19 @ X20 @ ( k3_subset_1 @ X19 @ X20 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('64',plain,
    ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['57','64'])).

thf('66',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['56','65'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('68',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('71',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('80',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k2_pre_topc @ X37 @ X36 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 @ ( k2_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69','84'])).

thf('86',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['56','65'])).

thf('87',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('89',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X30 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('90',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['87','93'])).

thf('95',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BjqZPobMVZ
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.48/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.71  % Solved by: fo/fo7.sh
% 0.48/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.71  % done 678 iterations in 0.257s
% 0.48/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.71  % SZS output start Refutation
% 0.48/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.71  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.48/0.71  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.48/0.71  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.48/0.71  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.48/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.48/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.48/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.71  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.48/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.71  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.48/0.71  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.48/0.71  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.48/0.71  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.48/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.71  thf(t77_tops_1, conjecture,
% 0.48/0.71    (![A:$i]:
% 0.48/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.71       ( ![B:$i]:
% 0.48/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.71           ( ( v4_pre_topc @ B @ A ) <=>
% 0.48/0.71             ( ( k2_tops_1 @ A @ B ) =
% 0.48/0.71               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.48/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.71    (~( ![A:$i]:
% 0.48/0.71        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.71          ( ![B:$i]:
% 0.48/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.71              ( ( v4_pre_topc @ B @ A ) <=>
% 0.48/0.71                ( ( k2_tops_1 @ A @ B ) =
% 0.48/0.71                  ( k7_subset_1 @
% 0.48/0.71                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.48/0.71    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.48/0.71  thf('0', plain,
% 0.48/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71              (k1_tops_1 @ sk_A @ sk_B)))
% 0.48/0.71        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('1', plain,
% 0.48/0.71      (~
% 0.48/0.71       (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.48/0.71       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.71      inference('split', [status(esa)], ['0'])).
% 0.48/0.71  thf('2', plain,
% 0.48/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71             (k1_tops_1 @ sk_A @ sk_B)))
% 0.48/0.71        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('3', plain,
% 0.48/0.71      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.71      inference('split', [status(esa)], ['2'])).
% 0.48/0.71  thf('4', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(t52_pre_topc, axiom,
% 0.48/0.71    (![A:$i]:
% 0.48/0.71     ( ( l1_pre_topc @ A ) =>
% 0.48/0.71       ( ![B:$i]:
% 0.48/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.71           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.48/0.71             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.48/0.71               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.48/0.71  thf('5', plain,
% 0.48/0.71      (![X26 : $i, X27 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.48/0.71          | ~ (v4_pre_topc @ X26 @ X27)
% 0.48/0.71          | ((k2_pre_topc @ X27 @ X26) = (X26))
% 0.48/0.71          | ~ (l1_pre_topc @ X27))),
% 0.48/0.71      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.48/0.71  thf('6', plain,
% 0.48/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.71        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.48/0.71        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.48/0.71  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('8', plain,
% 0.48/0.71      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.71      inference('demod', [status(thm)], ['6', '7'])).
% 0.48/0.71  thf('9', plain,
% 0.48/0.71      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.48/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['3', '8'])).
% 0.48/0.71  thf('10', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(l78_tops_1, axiom,
% 0.48/0.71    (![A:$i]:
% 0.48/0.71     ( ( l1_pre_topc @ A ) =>
% 0.48/0.71       ( ![B:$i]:
% 0.48/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.71           ( ( k2_tops_1 @ A @ B ) =
% 0.48/0.71             ( k7_subset_1 @
% 0.48/0.71               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.48/0.71               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.48/0.71  thf('11', plain,
% 0.48/0.71      (![X32 : $i, X33 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.48/0.71          | ((k2_tops_1 @ X33 @ X32)
% 0.48/0.71              = (k7_subset_1 @ (u1_struct_0 @ X33) @ 
% 0.48/0.71                 (k2_pre_topc @ X33 @ X32) @ (k1_tops_1 @ X33 @ X32)))
% 0.48/0.71          | ~ (l1_pre_topc @ X33))),
% 0.48/0.71      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.48/0.71  thf('12', plain,
% 0.48/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.71        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.48/0.71               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.71  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('14', plain,
% 0.48/0.71      (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.48/0.71            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.48/0.71  thf('15', plain,
% 0.48/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71             (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['9', '14'])).
% 0.48/0.71  thf('16', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(redefinition_k7_subset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.71       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.48/0.71  thf('17', plain,
% 0.48/0.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.48/0.71          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.48/0.71  thf('18', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.48/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.48/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.71  thf('19', plain,
% 0.48/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.71      inference('demod', [status(thm)], ['15', '18'])).
% 0.48/0.71  thf('20', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.48/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.48/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.71  thf('21', plain,
% 0.48/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71              (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('split', [status(esa)], ['0'])).
% 0.48/0.71  thf('22', plain,
% 0.48/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.48/0.71  thf('23', plain,
% 0.48/0.71      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.48/0.71         <= (~
% 0.48/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.48/0.71             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['19', '22'])).
% 0.48/0.71  thf('24', plain,
% 0.48/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.48/0.71       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.71      inference('simplify', [status(thm)], ['23'])).
% 0.48/0.71  thf('25', plain,
% 0.48/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.48/0.71       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.71      inference('split', [status(esa)], ['2'])).
% 0.48/0.71  thf('26', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.48/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.48/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.48/0.71  thf('27', plain,
% 0.48/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71             (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('split', [status(esa)], ['2'])).
% 0.48/0.71  thf('28', plain,
% 0.48/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['26', '27'])).
% 0.48/0.71  thf('29', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(t44_tops_1, axiom,
% 0.48/0.71    (![A:$i]:
% 0.48/0.71     ( ( l1_pre_topc @ A ) =>
% 0.48/0.71       ( ![B:$i]:
% 0.48/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.71           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.48/0.71  thf('30', plain,
% 0.48/0.71      (![X34 : $i, X35 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.48/0.71          | (r1_tarski @ (k1_tops_1 @ X35 @ X34) @ X34)
% 0.48/0.71          | ~ (l1_pre_topc @ X35))),
% 0.48/0.71      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.48/0.71  thf('31', plain,
% 0.48/0.71      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.48/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.71  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('33', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.48/0.71      inference('demod', [status(thm)], ['31', '32'])).
% 0.48/0.71  thf(t3_subset, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.71  thf('34', plain,
% 0.48/0.71      (![X23 : $i, X25 : $i]:
% 0.48/0.71         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 0.48/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.71  thf('35', plain,
% 0.48/0.71      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.48/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.71  thf(dt_k3_subset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.71       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.48/0.71  thf('36', plain,
% 0.48/0.71      (![X11 : $i, X12 : $i]:
% 0.48/0.71         ((m1_subset_1 @ (k3_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 0.48/0.71          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.48/0.71      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.48/0.71  thf('37', plain,
% 0.48/0.71      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.48/0.71        (k1_zfmisc_1 @ sk_B))),
% 0.48/0.71      inference('sup-', [status(thm)], ['35', '36'])).
% 0.48/0.71  thf('38', plain,
% 0.48/0.71      (![X23 : $i, X24 : $i]:
% 0.48/0.71         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.71  thf('39', plain,
% 0.48/0.71      ((r1_tarski @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)),
% 0.48/0.71      inference('sup-', [status(thm)], ['37', '38'])).
% 0.48/0.71  thf('40', plain,
% 0.48/0.71      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.48/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.71  thf(d5_subset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.71       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.48/0.71  thf('41', plain,
% 0.48/0.71      (![X9 : $i, X10 : $i]:
% 0.48/0.71         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.48/0.71          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.48/0.71      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.48/0.71  thf('42', plain,
% 0.48/0.71      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.48/0.71         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['40', '41'])).
% 0.48/0.71  thf('43', plain,
% 0.48/0.71      ((r1_tarski @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)),
% 0.48/0.71      inference('demod', [status(thm)], ['39', '42'])).
% 0.48/0.71  thf('44', plain,
% 0.48/0.71      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.48/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['28', '43'])).
% 0.48/0.71  thf('45', plain,
% 0.48/0.71      (![X23 : $i, X25 : $i]:
% 0.48/0.71         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 0.48/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.71  thf('46', plain,
% 0.48/0.71      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.48/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['44', '45'])).
% 0.48/0.71  thf('47', plain,
% 0.48/0.71      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.48/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.71  thf(redefinition_k4_subset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.48/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.71       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.48/0.71  thf('48', plain,
% 0.48/0.71      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.48/0.71          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.48/0.71          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.48/0.71  thf('49', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.48/0.71            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 0.48/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['47', '48'])).
% 0.48/0.71  thf('50', plain,
% 0.48/0.71      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.71          (k2_tops_1 @ sk_A @ sk_B))
% 0.48/0.71          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.71             (k2_tops_1 @ sk_A @ sk_B))))
% 0.48/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['46', '49'])).
% 0.48/0.71  thf(commutativity_k2_tarski, axiom,
% 0.48/0.71    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.48/0.71  thf('51', plain,
% 0.48/0.71      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.48/0.71  thf(l51_zfmisc_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.48/0.71  thf('52', plain,
% 0.48/0.71      (![X6 : $i, X7 : $i]:
% 0.48/0.71         ((k3_tarski @ (k2_tarski @ X6 @ X7)) = (k2_xboole_0 @ X6 @ X7))),
% 0.48/0.71      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.48/0.71  thf('53', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('sup+', [status(thm)], ['51', '52'])).
% 0.48/0.71  thf('54', plain,
% 0.48/0.71      (![X6 : $i, X7 : $i]:
% 0.48/0.71         ((k3_tarski @ (k2_tarski @ X6 @ X7)) = (k2_xboole_0 @ X6 @ X7))),
% 0.48/0.71      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.48/0.71  thf('55', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('sup+', [status(thm)], ['53', '54'])).
% 0.48/0.71  thf('56', plain,
% 0.48/0.71      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.71          (k2_tops_1 @ sk_A @ sk_B))
% 0.48/0.71          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.71             (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('demod', [status(thm)], ['50', '55'])).
% 0.48/0.71  thf('57', plain,
% 0.48/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['26', '27'])).
% 0.48/0.71  thf('58', plain,
% 0.48/0.71      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.48/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.71  thf(t25_subset_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.71       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.48/0.71         ( k2_subset_1 @ A ) ) ))).
% 0.48/0.71  thf('59', plain,
% 0.48/0.71      (![X19 : $i, X20 : $i]:
% 0.48/0.71         (((k4_subset_1 @ X19 @ X20 @ (k3_subset_1 @ X19 @ X20))
% 0.48/0.71            = (k2_subset_1 @ X19))
% 0.48/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.48/0.71  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.48/0.71  thf('60', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.48/0.71      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.48/0.71  thf('61', plain,
% 0.48/0.71      (![X19 : $i, X20 : $i]:
% 0.48/0.71         (((k4_subset_1 @ X19 @ X20 @ (k3_subset_1 @ X19 @ X20)) = (X19))
% 0.48/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.48/0.71      inference('demod', [status(thm)], ['59', '60'])).
% 0.48/0.71  thf('62', plain,
% 0.48/0.71      (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.71         (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 0.48/0.71      inference('sup-', [status(thm)], ['58', '61'])).
% 0.48/0.71  thf('63', plain,
% 0.48/0.71      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.48/0.71         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['40', '41'])).
% 0.48/0.71  thf('64', plain,
% 0.48/0.71      (((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.71         (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 0.48/0.71      inference('demod', [status(thm)], ['62', '63'])).
% 0.48/0.71  thf('65', plain,
% 0.48/0.71      ((((k4_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.71          (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.48/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['57', '64'])).
% 0.48/0.71  thf('66', plain,
% 0.48/0.71      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.48/0.71          = (sk_B)))
% 0.48/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['56', '65'])).
% 0.48/0.71  thf(t6_xboole_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.48/0.71  thf('67', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]:
% 0.48/0.71         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3))
% 0.48/0.71           = (k2_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.48/0.71  thf('68', plain,
% 0.48/0.71      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.48/0.71          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.71             (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['66', '67'])).
% 0.48/0.71  thf('69', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('sup+', [status(thm)], ['53', '54'])).
% 0.48/0.71  thf('70', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(dt_k2_tops_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( ( l1_pre_topc @ A ) & 
% 0.48/0.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.48/0.71       ( m1_subset_1 @
% 0.48/0.71         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.48/0.71  thf('71', plain,
% 0.48/0.71      (![X28 : $i, X29 : $i]:
% 0.48/0.71         (~ (l1_pre_topc @ X28)
% 0.48/0.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.48/0.71          | (m1_subset_1 @ (k2_tops_1 @ X28 @ X29) @ 
% 0.48/0.71             (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 0.48/0.71      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.48/0.71  thf('72', plain,
% 0.48/0.71      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.71         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.71        | ~ (l1_pre_topc @ sk_A))),
% 0.48/0.71      inference('sup-', [status(thm)], ['70', '71'])).
% 0.48/0.71  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('74', plain,
% 0.48/0.71      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.71      inference('demod', [status(thm)], ['72', '73'])).
% 0.48/0.71  thf('75', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('76', plain,
% 0.48/0.71      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.48/0.71          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.48/0.71          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.48/0.71      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.48/0.71  thf('77', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.48/0.71            = (k2_xboole_0 @ sk_B @ X0))
% 0.48/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['75', '76'])).
% 0.48/0.71  thf('78', plain,
% 0.48/0.71      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.48/0.71         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('sup-', [status(thm)], ['74', '77'])).
% 0.48/0.71  thf('79', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(t65_tops_1, axiom,
% 0.48/0.71    (![A:$i]:
% 0.48/0.71     ( ( l1_pre_topc @ A ) =>
% 0.48/0.71       ( ![B:$i]:
% 0.48/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.71           ( ( k2_pre_topc @ A @ B ) =
% 0.48/0.71             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.48/0.71  thf('80', plain,
% 0.48/0.71      (![X36 : $i, X37 : $i]:
% 0.48/0.71         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.48/0.71          | ((k2_pre_topc @ X37 @ X36)
% 0.48/0.71              = (k4_subset_1 @ (u1_struct_0 @ X37) @ X36 @ 
% 0.48/0.71                 (k2_tops_1 @ X37 @ X36)))
% 0.48/0.71          | ~ (l1_pre_topc @ X37))),
% 0.48/0.71      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.48/0.71  thf('81', plain,
% 0.48/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.71        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.48/0.71            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.48/0.71      inference('sup-', [status(thm)], ['79', '80'])).
% 0.48/0.71  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('83', plain,
% 0.48/0.71      (((k2_pre_topc @ sk_A @ sk_B)
% 0.48/0.71         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('demod', [status(thm)], ['81', '82'])).
% 0.48/0.71  thf('84', plain,
% 0.48/0.71      (((k2_pre_topc @ sk_A @ sk_B)
% 0.48/0.71         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['78', '83'])).
% 0.48/0.71  thf('85', plain,
% 0.48/0.71      ((((k2_pre_topc @ sk_A @ sk_B)
% 0.48/0.71          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.71             (k1_tops_1 @ sk_A @ sk_B))))
% 0.48/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('demod', [status(thm)], ['68', '69', '84'])).
% 0.48/0.71  thf('86', plain,
% 0.48/0.71      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.48/0.71          = (sk_B)))
% 0.48/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['56', '65'])).
% 0.48/0.71  thf('87', plain,
% 0.48/0.71      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.48/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['85', '86'])).
% 0.48/0.71  thf('88', plain,
% 0.48/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(fc1_tops_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.48/0.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.48/0.71       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.48/0.71  thf('89', plain,
% 0.48/0.71      (![X30 : $i, X31 : $i]:
% 0.48/0.71         (~ (l1_pre_topc @ X30)
% 0.48/0.71          | ~ (v2_pre_topc @ X30)
% 0.48/0.71          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.48/0.71          | (v4_pre_topc @ (k2_pre_topc @ X30 @ X31) @ X30))),
% 0.48/0.71      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.48/0.71  thf('90', plain,
% 0.48/0.71      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.48/0.71        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.71        | ~ (l1_pre_topc @ sk_A))),
% 0.48/0.71      inference('sup-', [status(thm)], ['88', '89'])).
% 0.48/0.71  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf('93', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.48/0.71      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.48/0.71  thf('94', plain,
% 0.48/0.71      (((v4_pre_topc @ sk_B @ sk_A))
% 0.48/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['87', '93'])).
% 0.48/0.71  thf('95', plain,
% 0.48/0.71      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.71      inference('split', [status(esa)], ['0'])).
% 0.48/0.71  thf('96', plain,
% 0.48/0.71      (~
% 0.48/0.71       (((k2_tops_1 @ sk_A @ sk_B)
% 0.48/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.48/0.71             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.48/0.71       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.48/0.71      inference('sup-', [status(thm)], ['94', '95'])).
% 0.48/0.71  thf('97', plain, ($false),
% 0.48/0.71      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '96'])).
% 0.48/0.71  
% 0.48/0.71  % SZS output end Refutation
% 0.48/0.71  
% 0.55/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
