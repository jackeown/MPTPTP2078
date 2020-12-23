%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dSQwBEJqBh

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:49 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 363 expanded)
%              Number of leaves         :   37 ( 127 expanded)
%              Depth                    :   21
%              Number of atoms          : 1297 (3522 expanded)
%              Number of equality atoms :  121 ( 336 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v4_pre_topc @ X23 @ X24 )
      | ( ( k2_pre_topc @ X24 @ X23 )
        = X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k2_tops_1 @ X28 @ X27 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X28 ) @ ( k2_pre_topc @ X28 @ X27 ) @ ( k1_tops_1 @ X28 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('36',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k2_pre_topc @ X30 @ X29 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ ( k2_tops_1 @ X30 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k4_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('50',plain,
    ( ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X13 @ X14 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X13 @ X14 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','55'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('58',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k4_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('60',plain,
    ( ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k4_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('65',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k4_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','73'])).

thf('75',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k4_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','85'])).

thf('87',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('89',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('91',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['75','95'])).

thf('97',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_pre_topc @ X24 )
      | ( ( k2_pre_topc @ X24 @ X23 )
       != X23 )
      | ( v4_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('107',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dSQwBEJqBh
% 0.13/0.37  % Computer   : n002.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 16:51:37 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.24/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.55  % Solved by: fo/fo7.sh
% 0.24/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.55  % done 139 iterations in 0.061s
% 0.24/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.55  % SZS output start Refutation
% 0.24/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.24/0.55  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.24/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.24/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.55  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.24/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.24/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.55  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.24/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.24/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.24/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.24/0.55  thf(t77_tops_1, conjecture,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.55       ( ![B:$i]:
% 0.24/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.55           ( ( v4_pre_topc @ B @ A ) <=>
% 0.24/0.55             ( ( k2_tops_1 @ A @ B ) =
% 0.24/0.55               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.24/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.55    (~( ![A:$i]:
% 0.24/0.55        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.55          ( ![B:$i]:
% 0.24/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.55              ( ( v4_pre_topc @ B @ A ) <=>
% 0.24/0.55                ( ( k2_tops_1 @ A @ B ) =
% 0.24/0.55                  ( k7_subset_1 @
% 0.24/0.55                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.24/0.55    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.24/0.55  thf('0', plain,
% 0.24/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55              (k1_tops_1 @ sk_A @ sk_B)))
% 0.24/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('1', plain,
% 0.24/0.55      (~
% 0.24/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.24/0.55       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.55      inference('split', [status(esa)], ['0'])).
% 0.24/0.55  thf('2', plain,
% 0.24/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55             (k1_tops_1 @ sk_A @ sk_B)))
% 0.24/0.55        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('3', plain,
% 0.24/0.55      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.55      inference('split', [status(esa)], ['2'])).
% 0.24/0.55  thf('4', plain,
% 0.24/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(t52_pre_topc, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( l1_pre_topc @ A ) =>
% 0.24/0.55       ( ![B:$i]:
% 0.24/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.55           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.24/0.55             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.24/0.55               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.24/0.55  thf('5', plain,
% 0.24/0.55      (![X23 : $i, X24 : $i]:
% 0.24/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.24/0.55          | ~ (v4_pre_topc @ X23 @ X24)
% 0.24/0.55          | ((k2_pre_topc @ X24 @ X23) = (X23))
% 0.24/0.55          | ~ (l1_pre_topc @ X24))),
% 0.24/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.24/0.55  thf('6', plain,
% 0.24/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.55        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.24/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.55  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('8', plain,
% 0.24/0.55      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.24/0.55  thf('9', plain,
% 0.24/0.55      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.24/0.55         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['3', '8'])).
% 0.24/0.55  thf('10', plain,
% 0.24/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(l78_tops_1, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( l1_pre_topc @ A ) =>
% 0.24/0.55       ( ![B:$i]:
% 0.24/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.55           ( ( k2_tops_1 @ A @ B ) =
% 0.24/0.55             ( k7_subset_1 @
% 0.24/0.55               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.24/0.55               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.24/0.55  thf('11', plain,
% 0.24/0.55      (![X27 : $i, X28 : $i]:
% 0.24/0.55         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.24/0.55          | ((k2_tops_1 @ X28 @ X27)
% 0.24/0.55              = (k7_subset_1 @ (u1_struct_0 @ X28) @ 
% 0.24/0.55                 (k2_pre_topc @ X28 @ X27) @ (k1_tops_1 @ X28 @ X27)))
% 0.24/0.55          | ~ (l1_pre_topc @ X28))),
% 0.24/0.55      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.24/0.55  thf('12', plain,
% 0.24/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.55        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.24/0.55               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.55  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('14', plain,
% 0.24/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.24/0.55            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.24/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.24/0.55  thf('15', plain,
% 0.24/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55             (k1_tops_1 @ sk_A @ sk_B))))
% 0.24/0.55         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.55      inference('sup+', [status(thm)], ['9', '14'])).
% 0.24/0.55  thf('16', plain,
% 0.24/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(redefinition_k7_subset_1, axiom,
% 0.24/0.55    (![A:$i,B:$i,C:$i]:
% 0.24/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.55       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.24/0.55  thf('17', plain,
% 0.24/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.24/0.55         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.24/0.55          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 0.24/0.55      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.24/0.55  thf('18', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.24/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.24/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.55  thf('19', plain,
% 0.24/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.24/0.55         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.55      inference('demod', [status(thm)], ['15', '18'])).
% 0.24/0.55  thf('20', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.24/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.24/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.55  thf('21', plain,
% 0.24/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55              (k1_tops_1 @ sk_A @ sk_B))))
% 0.24/0.55         <= (~
% 0.24/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.55      inference('split', [status(esa)], ['0'])).
% 0.24/0.55  thf('22', plain,
% 0.24/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.24/0.55         <= (~
% 0.24/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.55  thf('23', plain,
% 0.24/0.55      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.55         <= (~
% 0.24/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.24/0.55             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['19', '22'])).
% 0.24/0.55  thf('24', plain,
% 0.24/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.24/0.55       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.24/0.55  thf('25', plain,
% 0.24/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.24/0.55       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.55      inference('split', [status(esa)], ['2'])).
% 0.24/0.55  thf('26', plain,
% 0.24/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(dt_k2_tops_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( ( l1_pre_topc @ A ) & 
% 0.24/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.24/0.55       ( m1_subset_1 @
% 0.24/0.55         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.24/0.55  thf('27', plain,
% 0.24/0.55      (![X25 : $i, X26 : $i]:
% 0.24/0.55         (~ (l1_pre_topc @ X25)
% 0.24/0.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.24/0.55          | (m1_subset_1 @ (k2_tops_1 @ X25 @ X26) @ 
% 0.24/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 0.24/0.55      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.24/0.55  thf('28', plain,
% 0.24/0.55      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.24/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.24/0.55  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('30', plain,
% 0.24/0.55      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.24/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.24/0.55  thf('31', plain,
% 0.24/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(redefinition_k4_subset_1, axiom,
% 0.24/0.55    (![A:$i,B:$i,C:$i]:
% 0.24/0.55     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.24/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.24/0.55       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.24/0.55  thf('32', plain,
% 0.24/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.24/0.55         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.24/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.24/0.55          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.24/0.55      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.24/0.55  thf('33', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.24/0.55            = (k2_xboole_0 @ sk_B @ X0))
% 0.24/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.24/0.55  thf('34', plain,
% 0.24/0.55      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.24/0.55         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['30', '33'])).
% 0.24/0.55  thf('35', plain,
% 0.24/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(t65_tops_1, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( l1_pre_topc @ A ) =>
% 0.24/0.55       ( ![B:$i]:
% 0.24/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.55           ( ( k2_pre_topc @ A @ B ) =
% 0.24/0.55             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.24/0.55  thf('36', plain,
% 0.24/0.55      (![X29 : $i, X30 : $i]:
% 0.24/0.55         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.24/0.55          | ((k2_pre_topc @ X30 @ X29)
% 0.24/0.55              = (k4_subset_1 @ (u1_struct_0 @ X30) @ X29 @ 
% 0.24/0.55                 (k2_tops_1 @ X30 @ X29)))
% 0.24/0.55          | ~ (l1_pre_topc @ X30))),
% 0.24/0.55      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.24/0.55  thf('37', plain,
% 0.24/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.55        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.24/0.55            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.24/0.55  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('39', plain,
% 0.24/0.55      (((k2_pre_topc @ sk_A @ sk_B)
% 0.24/0.55         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.24/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.24/0.55  thf('40', plain,
% 0.24/0.55      (((k2_pre_topc @ sk_A @ sk_B)
% 0.24/0.55         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.24/0.55      inference('sup+', [status(thm)], ['34', '39'])).
% 0.24/0.55  thf(commutativity_k2_tarski, axiom,
% 0.24/0.55    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.24/0.55  thf('41', plain,
% 0.24/0.55      (![X11 : $i, X12 : $i]:
% 0.24/0.55         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 0.24/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.24/0.55  thf(t12_setfam_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.24/0.55  thf('42', plain,
% 0.24/0.55      (![X21 : $i, X22 : $i]:
% 0.24/0.55         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 0.24/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.24/0.55  thf('43', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.55      inference('sup+', [status(thm)], ['41', '42'])).
% 0.24/0.55  thf('44', plain,
% 0.24/0.55      (![X21 : $i, X22 : $i]:
% 0.24/0.55         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 0.24/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.24/0.55  thf('45', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.55      inference('sup+', [status(thm)], ['43', '44'])).
% 0.24/0.55  thf('46', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.24/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.24/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.55  thf('47', plain,
% 0.24/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55             (k1_tops_1 @ sk_A @ sk_B))))
% 0.24/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.55      inference('split', [status(esa)], ['2'])).
% 0.24/0.55  thf('48', plain,
% 0.24/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.24/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.55      inference('sup+', [status(thm)], ['46', '47'])).
% 0.24/0.55  thf(t51_xboole_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.24/0.55       ( A ) ))).
% 0.24/0.55  thf('49', plain,
% 0.24/0.55      (![X5 : $i, X6 : $i]:
% 0.24/0.55         ((k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k4_xboole_0 @ X5 @ X6))
% 0.24/0.55           = (X5))),
% 0.24/0.55      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.24/0.55  thf('50', plain,
% 0.24/0.55      ((((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.24/0.55          (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.24/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.55      inference('sup+', [status(thm)], ['48', '49'])).
% 0.24/0.55  thf('51', plain,
% 0.24/0.55      (![X11 : $i, X12 : $i]:
% 0.24/0.55         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 0.24/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.24/0.55  thf(l51_zfmisc_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.24/0.55  thf('52', plain,
% 0.24/0.55      (![X13 : $i, X14 : $i]:
% 0.24/0.55         ((k3_tarski @ (k2_tarski @ X13 @ X14)) = (k2_xboole_0 @ X13 @ X14))),
% 0.24/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.24/0.55  thf('53', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.55      inference('sup+', [status(thm)], ['51', '52'])).
% 0.24/0.55  thf('54', plain,
% 0.24/0.55      (![X13 : $i, X14 : $i]:
% 0.24/0.55         ((k3_tarski @ (k2_tarski @ X13 @ X14)) = (k2_xboole_0 @ X13 @ X14))),
% 0.24/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.24/0.55  thf('55', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.55      inference('sup+', [status(thm)], ['53', '54'])).
% 0.24/0.55  thf('56', plain,
% 0.24/0.55      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.24/0.55          (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.24/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.55      inference('demod', [status(thm)], ['50', '55'])).
% 0.24/0.55  thf(t46_xboole_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.24/0.55  thf('57', plain,
% 0.24/0.55      (![X3 : $i, X4 : $i]:
% 0.24/0.55         ((k4_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (k1_xboole_0))),
% 0.24/0.55      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.24/0.55  thf('58', plain,
% 0.24/0.55      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.24/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.55      inference('sup+', [status(thm)], ['56', '57'])).
% 0.24/0.55  thf('59', plain,
% 0.24/0.55      (![X5 : $i, X6 : $i]:
% 0.24/0.55         ((k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k4_xboole_0 @ X5 @ X6))
% 0.24/0.55           = (X5))),
% 0.24/0.55      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.24/0.55  thf('60', plain,
% 0.24/0.55      ((((k2_xboole_0 @ (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.24/0.55          k1_xboole_0) = (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.55      inference('sup+', [status(thm)], ['58', '59'])).
% 0.24/0.55  thf(idempotence_k3_xboole_0, axiom,
% 0.24/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.24/0.55  thf('61', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.24/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.24/0.55  thf('62', plain,
% 0.24/0.55      (![X5 : $i, X6 : $i]:
% 0.24/0.55         ((k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k4_xboole_0 @ X5 @ X6))
% 0.24/0.55           = (X5))),
% 0.24/0.55      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.24/0.55  thf('63', plain,
% 0.24/0.55      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['61', '62'])).
% 0.24/0.55  thf('64', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.24/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.24/0.55  thf(t100_xboole_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.24/0.55  thf('65', plain,
% 0.24/0.55      (![X1 : $i, X2 : $i]:
% 0.24/0.55         ((k4_xboole_0 @ X1 @ X2)
% 0.24/0.55           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.24/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.24/0.55  thf('66', plain,
% 0.24/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['64', '65'])).
% 0.24/0.55  thf('67', plain,
% 0.24/0.55      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.24/0.55      inference('demod', [status(thm)], ['63', '66'])).
% 0.24/0.55  thf('68', plain,
% 0.24/0.55      (![X3 : $i, X4 : $i]:
% 0.24/0.55         ((k4_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (k1_xboole_0))),
% 0.24/0.55      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.24/0.55  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['67', '68'])).
% 0.24/0.55  thf('70', plain,
% 0.24/0.55      (![X5 : $i, X6 : $i]:
% 0.24/0.55         ((k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k4_xboole_0 @ X5 @ X6))
% 0.24/0.55           = (X5))),
% 0.24/0.55      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.24/0.55  thf('71', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (X0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['69', '70'])).
% 0.24/0.55  thf('72', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.24/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.24/0.55  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.24/0.55      inference('demod', [status(thm)], ['71', '72'])).
% 0.24/0.55  thf('74', plain,
% 0.24/0.55      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.24/0.55          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.55      inference('demod', [status(thm)], ['60', '73'])).
% 0.24/0.55  thf('75', plain,
% 0.24/0.55      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.24/0.55          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.24/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.55      inference('sup+', [status(thm)], ['45', '74'])).
% 0.24/0.55  thf('76', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.55      inference('sup+', [status(thm)], ['43', '44'])).
% 0.24/0.55  thf('77', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.55      inference('sup+', [status(thm)], ['53', '54'])).
% 0.24/0.55  thf('78', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.24/0.55      inference('demod', [status(thm)], ['71', '72'])).
% 0.24/0.55  thf('79', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['77', '78'])).
% 0.24/0.55  thf('80', plain,
% 0.24/0.55      (![X3 : $i, X4 : $i]:
% 0.24/0.55         ((k4_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (k1_xboole_0))),
% 0.24/0.55      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.24/0.55  thf('81', plain,
% 0.24/0.55      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['79', '80'])).
% 0.24/0.55  thf('82', plain,
% 0.24/0.55      (![X5 : $i, X6 : $i]:
% 0.24/0.55         ((k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k4_xboole_0 @ X5 @ X6))
% 0.24/0.55           = (X5))),
% 0.24/0.55      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.24/0.55  thf('83', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.24/0.55           = (k1_xboole_0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['81', '82'])).
% 0.24/0.55  thf('84', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.24/0.55      inference('demod', [status(thm)], ['71', '72'])).
% 0.24/0.55  thf('85', plain,
% 0.24/0.55      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.24/0.55      inference('demod', [status(thm)], ['83', '84'])).
% 0.24/0.55  thf('86', plain,
% 0.24/0.55      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['76', '85'])).
% 0.24/0.55  thf('87', plain,
% 0.24/0.55      (![X1 : $i, X2 : $i]:
% 0.24/0.55         ((k4_xboole_0 @ X1 @ X2)
% 0.24/0.55           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.24/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.24/0.55  thf('88', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['86', '87'])).
% 0.24/0.55  thf(t5_boole, axiom,
% 0.24/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.24/0.55  thf('89', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.24/0.55      inference('cnf', [status(esa)], [t5_boole])).
% 0.24/0.55  thf('90', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.24/0.55      inference('demod', [status(thm)], ['88', '89'])).
% 0.24/0.55  thf(t52_xboole_1, axiom,
% 0.24/0.55    (![A:$i,B:$i,C:$i]:
% 0.24/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.24/0.55       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.24/0.55  thf('91', plain,
% 0.24/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.55         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X9))
% 0.24/0.55           = (k2_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X9)))),
% 0.24/0.55      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.24/0.55  thf('92', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 0.24/0.55           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.24/0.55      inference('sup+', [status(thm)], ['90', '91'])).
% 0.24/0.55  thf('93', plain,
% 0.24/0.55      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['79', '80'])).
% 0.24/0.55  thf('94', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.24/0.55      inference('demod', [status(thm)], ['88', '89'])).
% 0.24/0.55  thf('95', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.24/0.55      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.24/0.55  thf('96', plain,
% 0.24/0.55      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.24/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.55      inference('sup+', [status(thm)], ['75', '95'])).
% 0.24/0.55  thf('97', plain,
% 0.24/0.55      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.24/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.55      inference('sup+', [status(thm)], ['40', '96'])).
% 0.24/0.55  thf('98', plain,
% 0.24/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('99', plain,
% 0.24/0.55      (![X23 : $i, X24 : $i]:
% 0.24/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.24/0.55          | ~ (v2_pre_topc @ X24)
% 0.24/0.55          | ((k2_pre_topc @ X24 @ X23) != (X23))
% 0.24/0.55          | (v4_pre_topc @ X23 @ X24)
% 0.24/0.55          | ~ (l1_pre_topc @ X24))),
% 0.24/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.24/0.55  thf('100', plain,
% 0.24/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.55        | (v4_pre_topc @ sk_B @ sk_A)
% 0.24/0.55        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.24/0.55        | ~ (v2_pre_topc @ sk_A))),
% 0.24/0.55      inference('sup-', [status(thm)], ['98', '99'])).
% 0.24/0.55  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('103', plain,
% 0.24/0.55      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.24/0.55      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.24/0.55  thf('104', plain,
% 0.24/0.55      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.24/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['97', '103'])).
% 0.24/0.55  thf('105', plain,
% 0.24/0.55      (((v4_pre_topc @ sk_B @ sk_A))
% 0.24/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.24/0.55      inference('simplify', [status(thm)], ['104'])).
% 0.24/0.55  thf('106', plain,
% 0.24/0.55      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.24/0.55      inference('split', [status(esa)], ['0'])).
% 0.24/0.55  thf('107', plain,
% 0.24/0.55      (~
% 0.24/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.24/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.24/0.55             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.24/0.55       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.24/0.55      inference('sup-', [status(thm)], ['105', '106'])).
% 0.24/0.55  thf('108', plain, ($false),
% 0.24/0.55      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '107'])).
% 0.24/0.55  
% 0.24/0.55  % SZS output end Refutation
% 0.24/0.55  
% 0.24/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
