%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oqYDJq4YWO

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:49 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 167 expanded)
%              Number of leaves         :   34 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          : 1020 (2111 expanded)
%              Number of equality atoms :   84 ( 138 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v4_pre_topc @ X21 @ X22 )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k2_tops_1 @ X26 @ X25 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k2_pre_topc @ X26 @ X25 ) @ ( k1_tops_1 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k4_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X11 @ X12 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X11 @ X12 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k4_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('50',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('52',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k2_pre_topc @ X28 @ X27 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X28 ) @ X27 @ ( k2_tops_1 @ X28 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('56',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('61',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','63'])).

thf('65',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_pre_topc @ X22 )
      | ( ( k2_pre_topc @ X22 @ X21 )
       != X21 )
      | ( v4_pre_topc @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oqYDJq4YWO
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 309 iterations in 0.139s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.40/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.60  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.40/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.60  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.40/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.40/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.60  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.40/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.40/0.60  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.40/0.60  thf(t77_tops_1, conjecture,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.60           ( ( v4_pre_topc @ B @ A ) <=>
% 0.40/0.60             ( ( k2_tops_1 @ A @ B ) =
% 0.40/0.60               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i]:
% 0.40/0.60        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.60          ( ![B:$i]:
% 0.40/0.60            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.60              ( ( v4_pre_topc @ B @ A ) <=>
% 0.40/0.60                ( ( k2_tops_1 @ A @ B ) =
% 0.40/0.60                  ( k7_subset_1 @
% 0.40/0.60                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60              (k1_tops_1 @ sk_A @ sk_B)))
% 0.40/0.60        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (~
% 0.40/0.60       (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.40/0.60       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.60      inference('split', [status(esa)], ['0'])).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60             (k1_tops_1 @ sk_A @ sk_B)))
% 0.40/0.60        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.60      inference('split', [status(esa)], ['2'])).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t52_pre_topc, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( l1_pre_topc @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.60           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.40/0.60             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.40/0.60               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      (![X21 : $i, X22 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.40/0.60          | ~ (v4_pre_topc @ X21 @ X22)
% 0.40/0.60          | ((k2_pre_topc @ X22 @ X21) = (X21))
% 0.40/0.60          | ~ (l1_pre_topc @ X22))),
% 0.40/0.60      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.60        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.40/0.60        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.60  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.40/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['3', '8'])).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(l78_tops_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( l1_pre_topc @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.60           ( ( k2_tops_1 @ A @ B ) =
% 0.40/0.60             ( k7_subset_1 @
% 0.40/0.60               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.40/0.60               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.40/0.60  thf('11', plain,
% 0.40/0.60      (![X25 : $i, X26 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.40/0.60          | ((k2_tops_1 @ X26 @ X25)
% 0.40/0.60              = (k7_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.40/0.60                 (k2_pre_topc @ X26 @ X25) @ (k1_tops_1 @ X26 @ X25)))
% 0.40/0.60          | ~ (l1_pre_topc @ X26))),
% 0.40/0.60      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.60        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.60               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.60  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.40/0.60            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.60      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60             (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['9', '14'])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(redefinition_k7_subset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.60       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.40/0.60          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.40/0.60      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.40/0.60           = (k4_xboole_0 @ sk_B @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.60  thf('19', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.60      inference('demod', [status(thm)], ['15', '18'])).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.40/0.60           = (k4_xboole_0 @ sk_B @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60              (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('split', [status(esa)], ['0'])).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.40/0.60             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['19', '22'])).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.40/0.60       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.60      inference('simplify', [status(thm)], ['23'])).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.40/0.60       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.60      inference('split', [status(esa)], ['2'])).
% 0.40/0.60  thf('26', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.40/0.60           = (k4_xboole_0 @ sk_B @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60             (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('split', [status(esa)], ['2'])).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['26', '27'])).
% 0.40/0.60  thf(t51_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.40/0.60       ( A ) ))).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      (![X7 : $i, X8 : $i]:
% 0.40/0.60         ((k2_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k4_xboole_0 @ X7 @ X8))
% 0.40/0.60           = (X7))),
% 0.40/0.60      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.40/0.60  thf(commutativity_k2_tarski, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.40/0.60  thf('30', plain,
% 0.40/0.60      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 0.40/0.60      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.40/0.60  thf(l51_zfmisc_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.60  thf('31', plain,
% 0.40/0.60      (![X11 : $i, X12 : $i]:
% 0.40/0.60         ((k3_tarski @ (k2_tarski @ X11 @ X12)) = (k2_xboole_0 @ X11 @ X12))),
% 0.40/0.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.60  thf('32', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.40/0.60      inference('sup+', [status(thm)], ['30', '31'])).
% 0.40/0.60  thf('33', plain,
% 0.40/0.60      (![X11 : $i, X12 : $i]:
% 0.40/0.60         ((k3_tarski @ (k2_tarski @ X11 @ X12)) = (k2_xboole_0 @ X11 @ X12))),
% 0.40/0.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.40/0.60      inference('sup+', [status(thm)], ['32', '33'])).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      (![X7 : $i, X8 : $i]:
% 0.40/0.60         ((k2_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 0.40/0.60           = (X7))),
% 0.40/0.60      inference('demod', [status(thm)], ['29', '34'])).
% 0.40/0.60  thf('36', plain,
% 0.40/0.60      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.40/0.60          (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['28', '35'])).
% 0.40/0.60  thf(t46_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.40/0.60  thf('37', plain,
% 0.40/0.60      (![X5 : $i, X6 : $i]:
% 0.40/0.60         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.40/0.60  thf('38', plain,
% 0.40/0.60      (![X7 : $i, X8 : $i]:
% 0.40/0.60         ((k2_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k4_xboole_0 @ X7 @ X8))
% 0.40/0.60           = (X7))),
% 0.40/0.60      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.40/0.60  thf('39', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 0.40/0.60           k1_xboole_0) = (X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['37', '38'])).
% 0.40/0.60  thf(t1_boole, axiom,
% 0.40/0.60    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.60  thf('40', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.40/0.60      inference('cnf', [status(esa)], [t1_boole])).
% 0.40/0.60  thf('41', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.40/0.60  thf('42', plain,
% 0.40/0.60      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.40/0.60          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['36', '41'])).
% 0.40/0.60  thf('43', plain,
% 0.40/0.60      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 0.40/0.60      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.40/0.60  thf(t12_setfam_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.60  thf('44', plain,
% 0.40/0.60      (![X19 : $i, X20 : $i]:
% 0.40/0.60         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.40/0.60      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.40/0.60  thf('45', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.60      inference('sup+', [status(thm)], ['43', '44'])).
% 0.40/0.60  thf('46', plain,
% 0.40/0.60      (![X19 : $i, X20 : $i]:
% 0.40/0.60         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.40/0.60      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.40/0.60  thf('47', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.60      inference('sup+', [status(thm)], ['45', '46'])).
% 0.40/0.60  thf('48', plain,
% 0.40/0.60      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.40/0.60          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('demod', [status(thm)], ['42', '47'])).
% 0.40/0.60  thf(t22_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.40/0.60  thf('49', plain,
% 0.40/0.60      (![X3 : $i, X4 : $i]:
% 0.40/0.60         ((k2_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)) = (X3))),
% 0.40/0.60      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.40/0.60  thf('50', plain,
% 0.40/0.60      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['48', '49'])).
% 0.40/0.60  thf('51', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t65_tops_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( l1_pre_topc @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.60           ( ( k2_pre_topc @ A @ B ) =
% 0.40/0.60             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.40/0.60  thf('52', plain,
% 0.40/0.60      (![X27 : $i, X28 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.40/0.60          | ((k2_pre_topc @ X28 @ X27)
% 0.40/0.60              = (k4_subset_1 @ (u1_struct_0 @ X28) @ X27 @ 
% 0.40/0.60                 (k2_tops_1 @ X28 @ X27)))
% 0.40/0.60          | ~ (l1_pre_topc @ X28))),
% 0.40/0.60      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.40/0.60  thf('53', plain,
% 0.40/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.60        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.40/0.60            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['51', '52'])).
% 0.40/0.60  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('55', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(dt_k2_tops_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( l1_pre_topc @ A ) & 
% 0.40/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.40/0.60       ( m1_subset_1 @
% 0.40/0.60         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.40/0.60  thf('56', plain,
% 0.40/0.60      (![X23 : $i, X24 : $i]:
% 0.40/0.60         (~ (l1_pre_topc @ X23)
% 0.40/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.40/0.60          | (m1_subset_1 @ (k2_tops_1 @ X23 @ X24) @ 
% 0.40/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.40/0.60  thf('57', plain,
% 0.40/0.60      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.40/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.60  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('59', plain,
% 0.40/0.60      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.40/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('demod', [status(thm)], ['57', '58'])).
% 0.40/0.60  thf('60', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(redefinition_k4_subset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.40/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.60       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.40/0.60  thf('61', plain,
% 0.40/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.40/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.40/0.60          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.40/0.60      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.40/0.60  thf('62', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.40/0.60            = (k2_xboole_0 @ sk_B @ X0))
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.40/0.60  thf('63', plain,
% 0.40/0.60      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.40/0.60         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['59', '62'])).
% 0.40/0.60  thf('64', plain,
% 0.40/0.60      (((k2_pre_topc @ sk_A @ sk_B)
% 0.40/0.60         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.60      inference('demod', [status(thm)], ['53', '54', '63'])).
% 0.40/0.60  thf('65', plain,
% 0.40/0.60      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['50', '64'])).
% 0.40/0.60  thf('66', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('67', plain,
% 0.40/0.60      (![X21 : $i, X22 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.40/0.60          | ~ (v2_pre_topc @ X22)
% 0.40/0.60          | ((k2_pre_topc @ X22 @ X21) != (X21))
% 0.40/0.60          | (v4_pre_topc @ X21 @ X22)
% 0.40/0.60          | ~ (l1_pre_topc @ X22))),
% 0.40/0.60      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.40/0.60  thf('68', plain,
% 0.40/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.60        | (v4_pre_topc @ sk_B @ sk_A)
% 0.40/0.60        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.40/0.60        | ~ (v2_pre_topc @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['66', '67'])).
% 0.40/0.60  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('71', plain,
% 0.40/0.60      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.40/0.60      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.40/0.60  thf('72', plain,
% 0.40/0.60      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['65', '71'])).
% 0.40/0.60  thf('73', plain,
% 0.40/0.60      (((v4_pre_topc @ sk_B @ sk_A))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('simplify', [status(thm)], ['72'])).
% 0.40/0.60  thf('74', plain,
% 0.40/0.60      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.60      inference('split', [status(esa)], ['0'])).
% 0.40/0.60  thf('75', plain,
% 0.40/0.60      (~
% 0.40/0.60       (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.40/0.60       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['73', '74'])).
% 0.40/0.60  thf('76', plain, ($false),
% 0.40/0.60      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '75'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
