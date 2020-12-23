%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0785FIVkvO

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:46 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 236 expanded)
%              Number of leaves         :   39 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          : 1159 (2582 expanded)
%              Number of equality atoms :   96 ( 196 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v4_pre_topc @ X24 @ X25 )
      | ( ( k2_pre_topc @ X25 @ X24 )
        = X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k2_tops_1 @ X31 @ X30 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_pre_topc @ X31 @ X30 ) @ ( k1_tops_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('30',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('43',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('47',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('52',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','55'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('58',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('61',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('64',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('68',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k2_pre_topc @ X33 @ X32 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X33 ) @ X32 @ ( k2_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('72',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('73',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k4_subset_1 @ X17 @ X16 @ X18 )
        = ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','79'])).

thf('81',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['66','80'])).

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
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X28 @ X29 ) @ X28 ) ) ),
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
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0785FIVkvO
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 346 iterations in 0.113s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.38/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.38/0.57  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(t77_tops_1, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.57             ( ( k2_tops_1 @ A @ B ) =
% 0.38/0.57               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57          ( ![B:$i]:
% 0.38/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57              ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.57                ( ( k2_tops_1 @ A @ B ) =
% 0.38/0.57                  ( k7_subset_1 @
% 0.38/0.57                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57              (k1_tops_1 @ sk_A @ sk_B)))
% 0.38/0.57        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (~
% 0.38/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.38/0.57       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57             (k1_tops_1 @ sk_A @ sk_B)))
% 0.38/0.57        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.57      inference('split', [status(esa)], ['2'])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t52_pre_topc, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.38/0.57             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.38/0.57               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X24 : $i, X25 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.38/0.57          | ~ (v4_pre_topc @ X24 @ X25)
% 0.38/0.57          | ((k2_pre_topc @ X25 @ X24) = (X24))
% 0.38/0.57          | ~ (l1_pre_topc @ X25))),
% 0.38/0.57      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.38/0.57        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.57  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.38/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['3', '8'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(l78_tops_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( k2_tops_1 @ A @ B ) =
% 0.38/0.57             ( k7_subset_1 @
% 0.38/0.57               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.38/0.57               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X30 : $i, X31 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.38/0.57          | ((k2_tops_1 @ X31 @ X30)
% 0.38/0.57              = (k7_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.38/0.57                 (k2_pre_topc @ X31 @ X30) @ (k1_tops_1 @ X31 @ X30)))
% 0.38/0.57          | ~ (l1_pre_topc @ X31))),
% 0.38/0.57      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.57  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.38/0.57            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57             (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['9', '14'])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k7_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.38/0.57          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['15', '18'])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57              (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.38/0.57             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '22'])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.38/0.57       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.57      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.38/0.57       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.57      inference('split', [status(esa)], ['2'])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57             (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('split', [status(esa)], ['2'])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['26', '27'])).
% 0.38/0.57  thf(t36_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.38/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.38/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['28', '29'])).
% 0.38/0.57  thf(t28_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (![X4 : $i, X5 : $i]:
% 0.38/0.57         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.38/0.57          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.38/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf(commutativity_k2_tarski, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i]:
% 0.38/0.57         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.57  thf(t12_setfam_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      (![X22 : $i, X23 : $i]:
% 0.38/0.57         ((k1_setfam_1 @ (k2_tarski @ X22 @ X23)) = (k3_xboole_0 @ X22 @ X23))),
% 0.38/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['33', '34'])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (![X22 : $i, X23 : $i]:
% 0.38/0.57         ((k1_setfam_1 @ (k2_tarski @ X22 @ X23)) = (k3_xboole_0 @ X22 @ X23))),
% 0.38/0.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.38/0.57          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.38/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('demod', [status(thm)], ['32', '37'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.38/0.57  thf(t100_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (![X1 : $i, X2 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X1 @ X2)
% 0.38/0.57           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['39', '40'])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.38/0.57          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.38/0.57             (k2_tops_1 @ sk_A @ sk_B))))
% 0.38/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['38', '41'])).
% 0.38/0.57  thf(t3_boole, axiom,
% 0.38/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.57  thf('43', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.38/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.57  thf(t48_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (![X10 : $i, X11 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.38/0.57           = (k3_xboole_0 @ X10 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['43', '44'])).
% 0.38/0.57  thf(idempotence_k3_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.38/0.57  thf('46', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.38/0.57  thf('47', plain,
% 0.38/0.57      (![X1 : $i, X2 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X1 @ X2)
% 0.38/0.57           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.57  thf('48', plain,
% 0.38/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['46', '47'])).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.57      inference('demod', [status(thm)], ['45', '48'])).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.38/0.57  thf('51', plain,
% 0.38/0.57      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['49', '50'])).
% 0.38/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.57  thf('52', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.38/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.57  thf('53', plain,
% 0.38/0.57      (![X4 : $i, X5 : $i]:
% 0.38/0.57         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.57  thf('54', plain,
% 0.38/0.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.57  thf('55', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.57      inference('demod', [status(thm)], ['51', '54'])).
% 0.38/0.57  thf('56', plain,
% 0.38/0.57      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.38/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('demod', [status(thm)], ['42', '55'])).
% 0.38/0.57  thf(t98_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.38/0.57  thf('57', plain,
% 0.38/0.57      (![X12 : $i, X13 : $i]:
% 0.38/0.57         ((k2_xboole_0 @ X12 @ X13)
% 0.38/0.57           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.38/0.57  thf('58', plain,
% 0.38/0.57      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.38/0.57          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.38/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['56', '57'])).
% 0.38/0.57  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.57      inference('demod', [status(thm)], ['51', '54'])).
% 0.38/0.57  thf('60', plain,
% 0.38/0.57      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.57      inference('demod', [status(thm)], ['45', '48'])).
% 0.38/0.57  thf('61', plain,
% 0.38/0.57      (![X1 : $i, X2 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X1 @ X2)
% 0.38/0.57           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.57  thf('62', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.38/0.57           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['60', '61'])).
% 0.38/0.57  thf('63', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.38/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.57  thf('64', plain,
% 0.38/0.57      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['62', '63'])).
% 0.38/0.57  thf('65', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['59', '64'])).
% 0.38/0.57  thf('66', plain,
% 0.38/0.57      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.38/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('demod', [status(thm)], ['58', '65'])).
% 0.38/0.57  thf('67', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t65_tops_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( k2_pre_topc @ A @ B ) =
% 0.38/0.57             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.57  thf('68', plain,
% 0.38/0.57      (![X32 : $i, X33 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.38/0.57          | ((k2_pre_topc @ X33 @ X32)
% 0.38/0.57              = (k4_subset_1 @ (u1_struct_0 @ X33) @ X32 @ 
% 0.38/0.57                 (k2_tops_1 @ X33 @ X32)))
% 0.38/0.57          | ~ (l1_pre_topc @ X33))),
% 0.38/0.57      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.38/0.57  thf('69', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.38/0.57            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.38/0.57  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('71', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(dt_k2_tops_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.38/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.57       ( m1_subset_1 @
% 0.38/0.57         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.57  thf('72', plain,
% 0.38/0.57      (![X26 : $i, X27 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ X26)
% 0.38/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.38/0.57          | (m1_subset_1 @ (k2_tops_1 @ X26 @ X27) @ 
% 0.38/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.38/0.57  thf('73', plain,
% 0.38/0.57      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.38/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.57  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('75', plain,
% 0.38/0.57      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.38/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['73', '74'])).
% 0.38/0.57  thf('76', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k4_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.38/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.57       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.57  thf('77', plain,
% 0.38/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.38/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17))
% 0.38/0.57          | ((k4_subset_1 @ X17 @ X16 @ X18) = (k2_xboole_0 @ X16 @ X18)))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.38/0.57  thf('78', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.57            = (k2_xboole_0 @ sk_B @ X0))
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['76', '77'])).
% 0.38/0.57  thf('79', plain,
% 0.38/0.57      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.38/0.57         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['75', '78'])).
% 0.38/0.57  thf('80', plain,
% 0.38/0.57      (((k2_pre_topc @ sk_A @ sk_B)
% 0.38/0.57         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['69', '70', '79'])).
% 0.38/0.57  thf('81', plain,
% 0.38/0.57      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.38/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['66', '80'])).
% 0.38/0.57  thf('82', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(fc1_tops_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.38/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.57       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.38/0.57  thf('83', plain,
% 0.38/0.57      (![X28 : $i, X29 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ X28)
% 0.38/0.57          | ~ (v2_pre_topc @ X28)
% 0.38/0.57          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.38/0.57          | (v4_pre_topc @ (k2_pre_topc @ X28 @ X29) @ X28))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.38/0.57  thf('84', plain,
% 0.38/0.57      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.38/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['82', '83'])).
% 0.38/0.57  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('87', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.38/0.57      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.38/0.57  thf('88', plain,
% 0.38/0.57      (((v4_pre_topc @ sk_B @ sk_A))
% 0.38/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['81', '87'])).
% 0.38/0.57  thf('89', plain,
% 0.38/0.57      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('90', plain,
% 0.38/0.57      (~
% 0.38/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.57             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.38/0.57       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['88', '89'])).
% 0.38/0.57  thf('91', plain, ($false),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '90'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
