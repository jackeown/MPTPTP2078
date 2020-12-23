%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b6fpNJe2jM

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:58 EST 2020

% Result     : Theorem 27.38s
% Output     : Refutation 27.38s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 647 expanded)
%              Number of leaves         :   36 ( 217 expanded)
%              Depth                    :   19
%              Number of atoms          : 1762 (5951 expanded)
%              Number of equality atoms :  140 ( 429 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v4_pre_topc @ X29 @ X30 )
      | ( ( k2_pre_topc @ X30 @ X29 )
        = X29 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k2_tops_1 @ X36 @ X35 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k2_pre_topc @ X36 @ X35 ) @ ( k1_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('30',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('43',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('57',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('69',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['63','66','71'])).

thf('73',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('74',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('77',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['72','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','79'])).

thf('81',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['32','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('83',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('84',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('87',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('88',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('89',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('90',plain,
    ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('92',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('94',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('97',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k4_subset_1 @ X21 @ X20 @ X22 )
        = ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['92','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('102',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( k2_pre_topc @ X38 @ X37 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 @ ( k2_tops_1 @ X38 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('103',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('107',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','105','106'])).

thf('108',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['81','107'])).

thf('109',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('110',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('113',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','105','106'])).

thf('114',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('116',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('118',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('120',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('124',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('126',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['118','121'])).

thf('132',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('133',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('139',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('145',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('146',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('147',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['130','143','144','151'])).

thf('153',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('156',plain,(
    ! [X0: $i] :
      ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['113','156'])).

thf('158',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','111','112','157'])).

thf('159',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('160',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X33 @ X34 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('161',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['158','164'])).

thf('166',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('167',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','167'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b6fpNJe2jM
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:05:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 27.38/27.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 27.38/27.60  % Solved by: fo/fo7.sh
% 27.38/27.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 27.38/27.60  % done 28026 iterations in 27.174s
% 27.38/27.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 27.38/27.60  % SZS output start Refutation
% 27.38/27.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 27.38/27.60  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 27.38/27.60  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 27.38/27.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 27.38/27.60  thf(sk_A_type, type, sk_A: $i).
% 27.38/27.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 27.38/27.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 27.38/27.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 27.38/27.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 27.38/27.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 27.38/27.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 27.38/27.60  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 27.38/27.60  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 27.38/27.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 27.38/27.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 27.38/27.60  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 27.38/27.60  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 27.38/27.60  thf(sk_B_type, type, sk_B: $i).
% 27.38/27.60  thf(t77_tops_1, conjecture,
% 27.38/27.60    (![A:$i]:
% 27.38/27.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 27.38/27.60       ( ![B:$i]:
% 27.38/27.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.38/27.60           ( ( v4_pre_topc @ B @ A ) <=>
% 27.38/27.60             ( ( k2_tops_1 @ A @ B ) =
% 27.38/27.60               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 27.38/27.60  thf(zf_stmt_0, negated_conjecture,
% 27.38/27.60    (~( ![A:$i]:
% 27.38/27.60        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 27.38/27.60          ( ![B:$i]:
% 27.38/27.60            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.38/27.60              ( ( v4_pre_topc @ B @ A ) <=>
% 27.38/27.60                ( ( k2_tops_1 @ A @ B ) =
% 27.38/27.60                  ( k7_subset_1 @
% 27.38/27.60                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 27.38/27.60    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 27.38/27.60  thf('0', plain,
% 27.38/27.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60              (k1_tops_1 @ sk_A @ sk_B)))
% 27.38/27.60        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf('1', plain,
% 27.38/27.60      (~
% 27.38/27.60       (((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 27.38/27.60       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 27.38/27.60      inference('split', [status(esa)], ['0'])).
% 27.38/27.60  thf('2', plain,
% 27.38/27.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60             (k1_tops_1 @ sk_A @ sk_B)))
% 27.38/27.60        | (v4_pre_topc @ sk_B @ sk_A))),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf('3', plain,
% 27.38/27.60      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 27.38/27.60      inference('split', [status(esa)], ['2'])).
% 27.38/27.60  thf('4', plain,
% 27.38/27.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf(t52_pre_topc, axiom,
% 27.38/27.60    (![A:$i]:
% 27.38/27.60     ( ( l1_pre_topc @ A ) =>
% 27.38/27.60       ( ![B:$i]:
% 27.38/27.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.38/27.60           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 27.38/27.60             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 27.38/27.60               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 27.38/27.60  thf('5', plain,
% 27.38/27.60      (![X29 : $i, X30 : $i]:
% 27.38/27.60         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 27.38/27.60          | ~ (v4_pre_topc @ X29 @ X30)
% 27.38/27.60          | ((k2_pre_topc @ X30 @ X29) = (X29))
% 27.38/27.60          | ~ (l1_pre_topc @ X30))),
% 27.38/27.60      inference('cnf', [status(esa)], [t52_pre_topc])).
% 27.38/27.60  thf('6', plain,
% 27.38/27.60      ((~ (l1_pre_topc @ sk_A)
% 27.38/27.60        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 27.38/27.60        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 27.38/27.60      inference('sup-', [status(thm)], ['4', '5'])).
% 27.38/27.60  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf('8', plain,
% 27.38/27.60      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 27.38/27.60      inference('demod', [status(thm)], ['6', '7'])).
% 27.38/27.60  thf('9', plain,
% 27.38/27.60      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 27.38/27.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 27.38/27.60      inference('sup-', [status(thm)], ['3', '8'])).
% 27.38/27.60  thf('10', plain,
% 27.38/27.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf(l78_tops_1, axiom,
% 27.38/27.60    (![A:$i]:
% 27.38/27.60     ( ( l1_pre_topc @ A ) =>
% 27.38/27.60       ( ![B:$i]:
% 27.38/27.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.38/27.60           ( ( k2_tops_1 @ A @ B ) =
% 27.38/27.60             ( k7_subset_1 @
% 27.38/27.60               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 27.38/27.60               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 27.38/27.60  thf('11', plain,
% 27.38/27.60      (![X35 : $i, X36 : $i]:
% 27.38/27.60         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 27.38/27.60          | ((k2_tops_1 @ X36 @ X35)
% 27.38/27.60              = (k7_subset_1 @ (u1_struct_0 @ X36) @ 
% 27.38/27.60                 (k2_pre_topc @ X36 @ X35) @ (k1_tops_1 @ X36 @ X35)))
% 27.38/27.60          | ~ (l1_pre_topc @ X36))),
% 27.38/27.60      inference('cnf', [status(esa)], [l78_tops_1])).
% 27.38/27.60  thf('12', plain,
% 27.38/27.60      ((~ (l1_pre_topc @ sk_A)
% 27.38/27.60        | ((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.38/27.60               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 27.38/27.60      inference('sup-', [status(thm)], ['10', '11'])).
% 27.38/27.60  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf('14', plain,
% 27.38/27.60      (((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 27.38/27.60            (k1_tops_1 @ sk_A @ sk_B)))),
% 27.38/27.60      inference('demod', [status(thm)], ['12', '13'])).
% 27.38/27.60  thf('15', plain,
% 27.38/27.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60             (k1_tops_1 @ sk_A @ sk_B))))
% 27.38/27.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 27.38/27.60      inference('sup+', [status(thm)], ['9', '14'])).
% 27.38/27.60  thf('16', plain,
% 27.38/27.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf(redefinition_k7_subset_1, axiom,
% 27.38/27.60    (![A:$i,B:$i,C:$i]:
% 27.38/27.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 27.38/27.60       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 27.38/27.60  thf('17', plain,
% 27.38/27.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 27.38/27.60         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 27.38/27.60          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 27.38/27.60      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 27.38/27.60  thf('18', plain,
% 27.38/27.60      (![X0 : $i]:
% 27.38/27.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 27.38/27.60           = (k4_xboole_0 @ sk_B @ X0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['16', '17'])).
% 27.38/27.60  thf('19', plain,
% 27.38/27.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 27.38/27.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 27.38/27.60      inference('demod', [status(thm)], ['15', '18'])).
% 27.38/27.60  thf('20', plain,
% 27.38/27.60      (![X0 : $i]:
% 27.38/27.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 27.38/27.60           = (k4_xboole_0 @ sk_B @ X0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['16', '17'])).
% 27.38/27.60  thf('21', plain,
% 27.38/27.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60              (k1_tops_1 @ sk_A @ sk_B))))
% 27.38/27.60         <= (~
% 27.38/27.60             (((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 27.38/27.60      inference('split', [status(esa)], ['0'])).
% 27.38/27.60  thf('22', plain,
% 27.38/27.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 27.38/27.60         <= (~
% 27.38/27.60             (((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 27.38/27.60      inference('sup-', [status(thm)], ['20', '21'])).
% 27.38/27.60  thf('23', plain,
% 27.38/27.60      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 27.38/27.60         <= (~
% 27.38/27.60             (((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 27.38/27.60             ((v4_pre_topc @ sk_B @ sk_A)))),
% 27.38/27.60      inference('sup-', [status(thm)], ['19', '22'])).
% 27.38/27.60  thf('24', plain,
% 27.38/27.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 27.38/27.60       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 27.38/27.60      inference('simplify', [status(thm)], ['23'])).
% 27.38/27.60  thf('25', plain,
% 27.38/27.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 27.38/27.60       ((v4_pre_topc @ sk_B @ sk_A))),
% 27.38/27.60      inference('split', [status(esa)], ['2'])).
% 27.38/27.60  thf('26', plain,
% 27.38/27.60      (![X0 : $i]:
% 27.38/27.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 27.38/27.60           = (k4_xboole_0 @ sk_B @ X0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['16', '17'])).
% 27.38/27.60  thf('27', plain,
% 27.38/27.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60             (k1_tops_1 @ sk_A @ sk_B))))
% 27.38/27.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 27.38/27.60      inference('split', [status(esa)], ['2'])).
% 27.38/27.60  thf('28', plain,
% 27.38/27.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 27.38/27.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 27.38/27.60      inference('sup+', [status(thm)], ['26', '27'])).
% 27.38/27.60  thf(t36_xboole_1, axiom,
% 27.38/27.60    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 27.38/27.60  thf('29', plain,
% 27.38/27.60      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 27.38/27.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 27.38/27.60  thf('30', plain,
% 27.38/27.60      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 27.38/27.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 27.38/27.60      inference('sup+', [status(thm)], ['28', '29'])).
% 27.38/27.60  thf(t12_xboole_1, axiom,
% 27.38/27.60    (![A:$i,B:$i]:
% 27.38/27.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 27.38/27.60  thf('31', plain,
% 27.38/27.60      (![X5 : $i, X6 : $i]:
% 27.38/27.60         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 27.38/27.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 27.38/27.60  thf('32', plain,
% 27.38/27.60      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B)))
% 27.38/27.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 27.38/27.60      inference('sup-', [status(thm)], ['30', '31'])).
% 27.38/27.60  thf('33', plain,
% 27.38/27.60      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 27.38/27.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 27.38/27.60  thf(t44_xboole_1, axiom,
% 27.38/27.60    (![A:$i,B:$i,C:$i]:
% 27.38/27.60     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 27.38/27.60       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 27.38/27.60  thf('34', plain,
% 27.38/27.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 27.38/27.60         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 27.38/27.60          | ~ (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17))),
% 27.38/27.60      inference('cnf', [status(esa)], [t44_xboole_1])).
% 27.38/27.60  thf('35', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['33', '34'])).
% 27.38/27.60  thf('36', plain,
% 27.38/27.60      (![X5 : $i, X6 : $i]:
% 27.38/27.60         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 27.38/27.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 27.38/27.60  thf('37', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]:
% 27.38/27.60         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 27.38/27.60           = (k2_xboole_0 @ X1 @ X0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['35', '36'])).
% 27.38/27.60  thf(t48_xboole_1, axiom,
% 27.38/27.60    (![A:$i,B:$i]:
% 27.38/27.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 27.38/27.60  thf('38', plain,
% 27.38/27.60      (![X18 : $i, X19 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 27.38/27.60           = (k3_xboole_0 @ X18 @ X19))),
% 27.38/27.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 27.38/27.60  thf('39', plain,
% 27.38/27.60      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 27.38/27.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 27.38/27.60  thf('40', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 27.38/27.60      inference('sup+', [status(thm)], ['38', '39'])).
% 27.38/27.60  thf('41', plain,
% 27.38/27.60      (![X5 : $i, X6 : $i]:
% 27.38/27.60         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 27.38/27.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 27.38/27.60  thf('42', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]:
% 27.38/27.60         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['40', '41'])).
% 27.38/27.60  thf(t1_boole, axiom,
% 27.38/27.60    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 27.38/27.60  thf('43', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 27.38/27.60      inference('cnf', [status(esa)], [t1_boole])).
% 27.38/27.60  thf('44', plain,
% 27.38/27.60      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 27.38/27.60      inference('sup+', [status(thm)], ['42', '43'])).
% 27.38/27.60  thf(commutativity_k3_xboole_0, axiom,
% 27.38/27.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 27.38/27.60  thf('45', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 27.38/27.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 27.38/27.60  thf('46', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 27.38/27.60      inference('sup+', [status(thm)], ['38', '39'])).
% 27.38/27.60  thf('47', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 27.38/27.60      inference('sup+', [status(thm)], ['45', '46'])).
% 27.38/27.60  thf('48', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 27.38/27.60      inference('sup+', [status(thm)], ['44', '47'])).
% 27.38/27.60  thf('49', plain,
% 27.38/27.60      (![X5 : $i, X6 : $i]:
% 27.38/27.60         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 27.38/27.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 27.38/27.60  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['48', '49'])).
% 27.38/27.60  thf(d10_xboole_0, axiom,
% 27.38/27.60    (![A:$i,B:$i]:
% 27.38/27.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 27.38/27.60  thf('51', plain,
% 27.38/27.60      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 27.38/27.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.38/27.60  thf('52', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 27.38/27.60      inference('simplify', [status(thm)], ['51'])).
% 27.38/27.60  thf('53', plain,
% 27.38/27.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 27.38/27.60         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 27.38/27.60          | ~ (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17))),
% 27.38/27.60      inference('cnf', [status(esa)], [t44_xboole_1])).
% 27.38/27.60  thf('54', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]:
% 27.38/27.60         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 27.38/27.60      inference('sup-', [status(thm)], ['52', '53'])).
% 27.38/27.60  thf('55', plain,
% 27.38/27.60      (![X0 : $i]: (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 27.38/27.60      inference('sup+', [status(thm)], ['50', '54'])).
% 27.38/27.60  thf('56', plain,
% 27.38/27.60      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 27.38/27.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 27.38/27.60  thf('57', plain,
% 27.38/27.60      (![X2 : $i, X4 : $i]:
% 27.38/27.60         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 27.38/27.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.38/27.60  thf('58', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]:
% 27.38/27.60         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 27.38/27.60          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 27.38/27.60      inference('sup-', [status(thm)], ['56', '57'])).
% 27.38/27.60  thf('59', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['55', '58'])).
% 27.38/27.60  thf('60', plain,
% 27.38/27.60      (![X18 : $i, X19 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 27.38/27.60           = (k3_xboole_0 @ X18 @ X19))),
% 27.38/27.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 27.38/27.60  thf(t41_xboole_1, axiom,
% 27.38/27.60    (![A:$i,B:$i,C:$i]:
% 27.38/27.60     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 27.38/27.60       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 27.38/27.60  thf('61', plain,
% 27.38/27.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 27.38/27.60           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 27.38/27.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 27.38/27.60  thf('62', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 27.38/27.60           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 27.38/27.60      inference('sup+', [status(thm)], ['60', '61'])).
% 27.38/27.60  thf('63', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 27.38/27.60           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 27.38/27.60      inference('sup+', [status(thm)], ['59', '62'])).
% 27.38/27.60  thf('64', plain,
% 27.38/27.60      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 27.38/27.60      inference('sup+', [status(thm)], ['42', '43'])).
% 27.38/27.60  thf('65', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 27.38/27.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 27.38/27.60  thf('66', plain,
% 27.38/27.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 27.38/27.60      inference('sup+', [status(thm)], ['64', '65'])).
% 27.38/27.60  thf('67', plain,
% 27.38/27.60      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 27.38/27.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 27.38/27.60  thf('68', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 27.38/27.60      inference('sup+', [status(thm)], ['44', '47'])).
% 27.38/27.60  thf('69', plain,
% 27.38/27.60      (![X2 : $i, X4 : $i]:
% 27.38/27.60         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 27.38/27.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.38/27.60  thf('70', plain,
% 27.38/27.60      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 27.38/27.60      inference('sup-', [status(thm)], ['68', '69'])).
% 27.38/27.60  thf('71', plain,
% 27.38/27.60      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['67', '70'])).
% 27.38/27.60  thf('72', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]:
% 27.38/27.60         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 27.38/27.60      inference('demod', [status(thm)], ['63', '66', '71'])).
% 27.38/27.60  thf('73', plain,
% 27.38/27.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 27.38/27.60           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 27.38/27.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 27.38/27.60  thf('74', plain,
% 27.38/27.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 27.38/27.60           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 27.38/27.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 27.38/27.60  thf('75', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 27.38/27.60           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 27.38/27.60      inference('sup+', [status(thm)], ['73', '74'])).
% 27.38/27.60  thf('76', plain,
% 27.38/27.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 27.38/27.60           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 27.38/27.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 27.38/27.60  thf('77', plain,
% 27.38/27.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 27.38/27.60           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 27.38/27.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 27.38/27.60  thf('78', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 27.38/27.60           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 27.38/27.60      inference('demod', [status(thm)], ['75', '76', '77'])).
% 27.38/27.60  thf('79', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.38/27.60         ((k1_xboole_0)
% 27.38/27.60           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ 
% 27.38/27.60              (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 27.38/27.60      inference('sup+', [status(thm)], ['72', '78'])).
% 27.38/27.60  thf('80', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]:
% 27.38/27.60         ((k1_xboole_0)
% 27.38/27.60           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 27.38/27.60      inference('sup+', [status(thm)], ['37', '79'])).
% 27.38/27.60  thf('81', plain,
% 27.38/27.60      ((((k1_xboole_0)
% 27.38/27.60          = (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 27.38/27.60             sk_B)))
% 27.38/27.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 27.38/27.60      inference('sup+', [status(thm)], ['32', '80'])).
% 27.38/27.60  thf('82', plain,
% 27.38/27.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf(dt_k2_tops_1, axiom,
% 27.38/27.60    (![A:$i,B:$i]:
% 27.38/27.60     ( ( ( l1_pre_topc @ A ) & 
% 27.38/27.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 27.38/27.60       ( m1_subset_1 @
% 27.38/27.60         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 27.38/27.60  thf('83', plain,
% 27.38/27.60      (![X31 : $i, X32 : $i]:
% 27.38/27.60         (~ (l1_pre_topc @ X31)
% 27.38/27.60          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 27.38/27.60          | (m1_subset_1 @ (k2_tops_1 @ X31 @ X32) @ 
% 27.38/27.60             (k1_zfmisc_1 @ (u1_struct_0 @ X31))))),
% 27.38/27.60      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 27.38/27.60  thf('84', plain,
% 27.38/27.60      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 27.38/27.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.38/27.60        | ~ (l1_pre_topc @ sk_A))),
% 27.38/27.60      inference('sup-', [status(thm)], ['82', '83'])).
% 27.38/27.60  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf('86', plain,
% 27.38/27.60      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 27.38/27.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.38/27.60      inference('demod', [status(thm)], ['84', '85'])).
% 27.38/27.60  thf(t3_subset, axiom,
% 27.38/27.60    (![A:$i,B:$i]:
% 27.38/27.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 27.38/27.60  thf('87', plain,
% 27.38/27.60      (![X26 : $i, X27 : $i]:
% 27.38/27.60         ((r1_tarski @ X26 @ X27) | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 27.38/27.60      inference('cnf', [status(esa)], [t3_subset])).
% 27.38/27.60  thf('88', plain,
% 27.38/27.60      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 27.38/27.60      inference('sup-', [status(thm)], ['86', '87'])).
% 27.38/27.60  thf(t28_xboole_1, axiom,
% 27.38/27.60    (![A:$i,B:$i]:
% 27.38/27.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 27.38/27.60  thf('89', plain,
% 27.38/27.60      (![X8 : $i, X9 : $i]:
% 27.38/27.60         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 27.38/27.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 27.38/27.60  thf('90', plain,
% 27.38/27.60      (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 27.38/27.60         = (k2_tops_1 @ sk_A @ sk_B))),
% 27.38/27.60      inference('sup-', [status(thm)], ['88', '89'])).
% 27.38/27.60  thf('91', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 27.38/27.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 27.38/27.60  thf('92', plain,
% 27.38/27.60      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 27.38/27.60         = (k2_tops_1 @ sk_A @ sk_B))),
% 27.38/27.60      inference('demod', [status(thm)], ['90', '91'])).
% 27.38/27.60  thf('93', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 27.38/27.60      inference('sup+', [status(thm)], ['38', '39'])).
% 27.38/27.60  thf('94', plain,
% 27.38/27.60      (![X26 : $i, X28 : $i]:
% 27.38/27.60         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 27.38/27.60      inference('cnf', [status(esa)], [t3_subset])).
% 27.38/27.60  thf('95', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]:
% 27.38/27.60         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['93', '94'])).
% 27.38/27.60  thf('96', plain,
% 27.38/27.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf(redefinition_k4_subset_1, axiom,
% 27.38/27.60    (![A:$i,B:$i,C:$i]:
% 27.38/27.60     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 27.38/27.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 27.38/27.60       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 27.38/27.60  thf('97', plain,
% 27.38/27.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 27.38/27.60         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 27.38/27.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 27.38/27.60          | ((k4_subset_1 @ X21 @ X20 @ X22) = (k2_xboole_0 @ X20 @ X22)))),
% 27.38/27.60      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 27.38/27.60  thf('98', plain,
% 27.38/27.60      (![X0 : $i]:
% 27.38/27.60         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 27.38/27.60            = (k2_xboole_0 @ sk_B @ X0))
% 27.38/27.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 27.38/27.60      inference('sup-', [status(thm)], ['96', '97'])).
% 27.38/27.60  thf('99', plain,
% 27.38/27.60      (![X0 : $i]:
% 27.38/27.60         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60           (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 27.38/27.60           = (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 27.38/27.60      inference('sup-', [status(thm)], ['95', '98'])).
% 27.38/27.60  thf('100', plain,
% 27.38/27.60      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 27.38/27.60         = (k2_xboole_0 @ sk_B @ 
% 27.38/27.60            (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 27.38/27.60      inference('sup+', [status(thm)], ['92', '99'])).
% 27.38/27.60  thf('101', plain,
% 27.38/27.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf(t65_tops_1, axiom,
% 27.38/27.60    (![A:$i]:
% 27.38/27.60     ( ( l1_pre_topc @ A ) =>
% 27.38/27.60       ( ![B:$i]:
% 27.38/27.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.38/27.60           ( ( k2_pre_topc @ A @ B ) =
% 27.38/27.60             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 27.38/27.60  thf('102', plain,
% 27.38/27.60      (![X37 : $i, X38 : $i]:
% 27.38/27.60         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 27.38/27.60          | ((k2_pre_topc @ X38 @ X37)
% 27.38/27.60              = (k4_subset_1 @ (u1_struct_0 @ X38) @ X37 @ 
% 27.38/27.60                 (k2_tops_1 @ X38 @ X37)))
% 27.38/27.60          | ~ (l1_pre_topc @ X38))),
% 27.38/27.60      inference('cnf', [status(esa)], [t65_tops_1])).
% 27.38/27.60  thf('103', plain,
% 27.38/27.60      ((~ (l1_pre_topc @ sk_A)
% 27.38/27.60        | ((k2_pre_topc @ sk_A @ sk_B)
% 27.38/27.60            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60               (k2_tops_1 @ sk_A @ sk_B))))),
% 27.38/27.60      inference('sup-', [status(thm)], ['101', '102'])).
% 27.38/27.60  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf('105', plain,
% 27.38/27.60      (((k2_pre_topc @ sk_A @ sk_B)
% 27.38/27.60         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60            (k2_tops_1 @ sk_A @ sk_B)))),
% 27.38/27.60      inference('demod', [status(thm)], ['103', '104'])).
% 27.38/27.60  thf('106', plain,
% 27.38/27.60      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 27.38/27.60         = (k2_tops_1 @ sk_A @ sk_B))),
% 27.38/27.60      inference('demod', [status(thm)], ['90', '91'])).
% 27.38/27.60  thf('107', plain,
% 27.38/27.60      (((k2_pre_topc @ sk_A @ sk_B)
% 27.38/27.60         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 27.38/27.60      inference('demod', [status(thm)], ['100', '105', '106'])).
% 27.38/27.60  thf('108', plain,
% 27.38/27.60      ((((k1_xboole_0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 27.38/27.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 27.38/27.60      inference('demod', [status(thm)], ['81', '107'])).
% 27.38/27.60  thf('109', plain,
% 27.38/27.60      (![X18 : $i, X19 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 27.38/27.60           = (k3_xboole_0 @ X18 @ X19))),
% 27.38/27.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 27.38/27.60  thf('110', plain,
% 27.38/27.60      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ k1_xboole_0)
% 27.38/27.60          = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 27.38/27.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 27.38/27.60      inference('sup+', [status(thm)], ['108', '109'])).
% 27.38/27.60  thf('111', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['55', '58'])).
% 27.38/27.60  thf('112', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 27.38/27.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 27.38/27.60  thf('113', plain,
% 27.38/27.60      (((k2_pre_topc @ sk_A @ sk_B)
% 27.38/27.60         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 27.38/27.60      inference('demod', [status(thm)], ['100', '105', '106'])).
% 27.38/27.60  thf('114', plain,
% 27.38/27.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf('115', plain,
% 27.38/27.60      (![X26 : $i, X27 : $i]:
% 27.38/27.60         ((r1_tarski @ X26 @ X27) | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 27.38/27.60      inference('cnf', [status(esa)], [t3_subset])).
% 27.38/27.60  thf('116', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 27.38/27.60      inference('sup-', [status(thm)], ['114', '115'])).
% 27.38/27.60  thf('117', plain,
% 27.38/27.60      (![X8 : $i, X9 : $i]:
% 27.38/27.60         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 27.38/27.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 27.38/27.60  thf('118', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 27.38/27.60      inference('sup-', [status(thm)], ['116', '117'])).
% 27.38/27.60  thf('119', plain,
% 27.38/27.60      (![X18 : $i, X19 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 27.38/27.60           = (k3_xboole_0 @ X18 @ X19))),
% 27.38/27.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 27.38/27.60  thf('120', plain,
% 27.38/27.60      (![X18 : $i, X19 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 27.38/27.60           = (k3_xboole_0 @ X18 @ X19))),
% 27.38/27.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 27.38/27.60  thf('121', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 27.38/27.60           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 27.38/27.60      inference('sup+', [status(thm)], ['119', '120'])).
% 27.38/27.60  thf('122', plain,
% 27.38/27.60      (((k4_xboole_0 @ sk_B @ sk_B)
% 27.38/27.60         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 27.38/27.60      inference('sup+', [status(thm)], ['118', '121'])).
% 27.38/27.60  thf('123', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 27.38/27.60      inference('sup+', [status(thm)], ['45', '46'])).
% 27.38/27.60  thf('124', plain,
% 27.38/27.60      ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_B) @ 
% 27.38/27.60        (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 27.38/27.60      inference('sup+', [status(thm)], ['122', '123'])).
% 27.38/27.60  thf('125', plain,
% 27.38/27.60      (![X26 : $i, X28 : $i]:
% 27.38/27.60         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 27.38/27.60      inference('cnf', [status(esa)], [t3_subset])).
% 27.38/27.60  thf('126', plain,
% 27.38/27.60      ((m1_subset_1 @ (k4_xboole_0 @ sk_B @ sk_B) @ 
% 27.38/27.60        (k1_zfmisc_1 @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 27.38/27.60      inference('sup-', [status(thm)], ['124', '125'])).
% 27.38/27.60  thf('127', plain,
% 27.38/27.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 27.38/27.60         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 27.38/27.60          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 27.38/27.60      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 27.38/27.60  thf('128', plain,
% 27.38/27.60      (![X0 : $i]:
% 27.38/27.60         ((k7_subset_1 @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 27.38/27.60           (k4_xboole_0 @ sk_B @ sk_B) @ X0)
% 27.38/27.60           = (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B) @ X0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['126', '127'])).
% 27.38/27.60  thf('129', plain,
% 27.38/27.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 27.38/27.60           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 27.38/27.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 27.38/27.60  thf('130', plain,
% 27.38/27.60      (![X0 : $i]:
% 27.38/27.60         ((k7_subset_1 @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 27.38/27.60           (k4_xboole_0 @ sk_B @ sk_B) @ X0)
% 27.38/27.60           = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ X0)))),
% 27.38/27.60      inference('demod', [status(thm)], ['128', '129'])).
% 27.38/27.60  thf('131', plain,
% 27.38/27.60      (((k4_xboole_0 @ sk_B @ sk_B)
% 27.38/27.60         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 27.38/27.60      inference('sup+', [status(thm)], ['118', '121'])).
% 27.38/27.60  thf('132', plain,
% 27.38/27.60      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 27.38/27.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 27.38/27.60  thf('133', plain,
% 27.38/27.60      (![X8 : $i, X9 : $i]:
% 27.38/27.60         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 27.38/27.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 27.38/27.60  thf('134', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]:
% 27.38/27.60         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 27.38/27.60           = (k4_xboole_0 @ X0 @ X1))),
% 27.38/27.60      inference('sup-', [status(thm)], ['132', '133'])).
% 27.38/27.60  thf('135', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 27.38/27.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 27.38/27.60  thf('136', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]:
% 27.38/27.60         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 27.38/27.60           = (k4_xboole_0 @ X0 @ X1))),
% 27.38/27.60      inference('demod', [status(thm)], ['134', '135'])).
% 27.38/27.60  thf('137', plain,
% 27.38/27.60      (((k4_xboole_0 @ sk_B @ sk_B)
% 27.38/27.60         = (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 27.38/27.60      inference('demod', [status(thm)], ['131', '136'])).
% 27.38/27.60  thf('138', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['55', '58'])).
% 27.38/27.60  thf('139', plain,
% 27.38/27.60      (![X18 : $i, X19 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 27.38/27.60           = (k3_xboole_0 @ X18 @ X19))),
% 27.38/27.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 27.38/27.60  thf('140', plain,
% 27.38/27.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 27.38/27.60      inference('sup+', [status(thm)], ['138', '139'])).
% 27.38/27.60  thf('141', plain,
% 27.38/27.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 27.38/27.60      inference('sup+', [status(thm)], ['64', '65'])).
% 27.38/27.60  thf('142', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 27.38/27.60      inference('demod', [status(thm)], ['140', '141'])).
% 27.38/27.60  thf('143', plain,
% 27.38/27.60      (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 27.38/27.60      inference('demod', [status(thm)], ['137', '142'])).
% 27.38/27.60  thf('144', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 27.38/27.60      inference('demod', [status(thm)], ['140', '141'])).
% 27.38/27.60  thf('145', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 27.38/27.60      inference('sup+', [status(thm)], ['44', '47'])).
% 27.38/27.60  thf('146', plain,
% 27.38/27.60      (![X26 : $i, X28 : $i]:
% 27.38/27.60         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 27.38/27.60      inference('cnf', [status(esa)], [t3_subset])).
% 27.38/27.60  thf('147', plain,
% 27.38/27.60      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['145', '146'])).
% 27.38/27.60  thf('148', plain,
% 27.38/27.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 27.38/27.60         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 27.38/27.60          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 27.38/27.60      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 27.38/27.60  thf('149', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]:
% 27.38/27.60         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1)
% 27.38/27.60           = (k4_xboole_0 @ k1_xboole_0 @ X1))),
% 27.38/27.60      inference('sup-', [status(thm)], ['147', '148'])).
% 27.38/27.60  thf('150', plain,
% 27.38/27.60      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['67', '70'])).
% 27.38/27.60  thf('151', plain,
% 27.38/27.60      (![X0 : $i, X1 : $i]:
% 27.38/27.60         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 27.38/27.60      inference('demod', [status(thm)], ['149', '150'])).
% 27.38/27.60  thf('152', plain,
% 27.38/27.60      (![X0 : $i]:
% 27.38/27.60         ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ X0)))),
% 27.38/27.60      inference('demod', [status(thm)], ['130', '143', '144', '151'])).
% 27.38/27.60  thf('153', plain,
% 27.38/27.60      (![X18 : $i, X19 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 27.38/27.60           = (k3_xboole_0 @ X18 @ X19))),
% 27.38/27.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 27.38/27.60  thf('154', plain,
% 27.38/27.60      (![X0 : $i]:
% 27.38/27.60         ((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 27.38/27.60           = (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ X0)))),
% 27.38/27.60      inference('sup+', [status(thm)], ['152', '153'])).
% 27.38/27.60  thf('155', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 27.38/27.60      inference('sup-', [status(thm)], ['55', '58'])).
% 27.38/27.60  thf('156', plain,
% 27.38/27.60      (![X0 : $i]: ((sk_B) = (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ X0)))),
% 27.38/27.60      inference('demod', [status(thm)], ['154', '155'])).
% 27.38/27.60  thf('157', plain,
% 27.38/27.60      (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 27.38/27.60      inference('sup+', [status(thm)], ['113', '156'])).
% 27.38/27.60  thf('158', plain,
% 27.38/27.60      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 27.38/27.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 27.38/27.60      inference('demod', [status(thm)], ['110', '111', '112', '157'])).
% 27.38/27.60  thf('159', plain,
% 27.38/27.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf(fc1_tops_1, axiom,
% 27.38/27.60    (![A:$i,B:$i]:
% 27.38/27.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 27.38/27.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 27.38/27.60       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 27.38/27.60  thf('160', plain,
% 27.38/27.60      (![X33 : $i, X34 : $i]:
% 27.38/27.60         (~ (l1_pre_topc @ X33)
% 27.38/27.60          | ~ (v2_pre_topc @ X33)
% 27.38/27.60          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 27.38/27.60          | (v4_pre_topc @ (k2_pre_topc @ X33 @ X34) @ X33))),
% 27.38/27.60      inference('cnf', [status(esa)], [fc1_tops_1])).
% 27.38/27.60  thf('161', plain,
% 27.38/27.60      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 27.38/27.60        | ~ (v2_pre_topc @ sk_A)
% 27.38/27.60        | ~ (l1_pre_topc @ sk_A))),
% 27.38/27.60      inference('sup-', [status(thm)], ['159', '160'])).
% 27.38/27.60  thf('162', plain, ((v2_pre_topc @ sk_A)),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf('163', plain, ((l1_pre_topc @ sk_A)),
% 27.38/27.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.38/27.60  thf('164', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 27.38/27.60      inference('demod', [status(thm)], ['161', '162', '163'])).
% 27.38/27.60  thf('165', plain,
% 27.38/27.60      (((v4_pre_topc @ sk_B @ sk_A))
% 27.38/27.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 27.38/27.60      inference('sup+', [status(thm)], ['158', '164'])).
% 27.38/27.60  thf('166', plain,
% 27.38/27.60      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 27.38/27.60      inference('split', [status(esa)], ['0'])).
% 27.38/27.60  thf('167', plain,
% 27.38/27.60      (~
% 27.38/27.60       (((k2_tops_1 @ sk_A @ sk_B)
% 27.38/27.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 27.38/27.60             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 27.38/27.60       ((v4_pre_topc @ sk_B @ sk_A))),
% 27.38/27.60      inference('sup-', [status(thm)], ['165', '166'])).
% 27.38/27.60  thf('168', plain, ($false),
% 27.38/27.60      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '167'])).
% 27.38/27.60  
% 27.38/27.60  % SZS output end Refutation
% 27.38/27.60  
% 27.38/27.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
