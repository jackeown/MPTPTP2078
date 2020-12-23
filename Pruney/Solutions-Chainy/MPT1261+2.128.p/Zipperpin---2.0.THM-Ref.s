%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pw3ZfB9NZk

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 141 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  881 (1954 expanded)
%              Number of equality atoms :   65 ( 116 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_pre_topc @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_tops_1 @ X18 @ X17 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_pre_topc @ X18 @ X17 ) @ ( k1_tops_1 @ X18 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
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

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ ( k2_tops_1 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k4_subset_1 @ X10 @ X9 @ X11 )
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('49',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['39','48'])).

thf('50',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_pre_topc @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
       != X15 )
      | ( v4_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pw3ZfB9NZk
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:13:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 77 iterations in 0.038s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.48  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.48  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(t77_tops_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.48             ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.48               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48              ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.48                ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.48                  ( k7_subset_1 @
% 0.20/0.48                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48              (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.48        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (~
% 0.20/0.48       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.48       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48             (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.48        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t52_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.48             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.48               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.48          | ~ (v4_pre_topc @ X15 @ X16)
% 0.20/0.48          | ((k2_pre_topc @ X16 @ X15) = (X15))
% 0.20/0.48          | ~ (l1_pre_topc @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.20/0.48        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.48         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(l78_tops_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.48             ( k7_subset_1 @
% 0.20/0.48               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.20/0.48               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X17 : $i, X18 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.48          | ((k2_tops_1 @ X18 @ X17)
% 0.20/0.48              = (k7_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.20/0.48                 (k2_pre_topc @ X18 @ X17) @ (k1_tops_1 @ X18 @ X17)))
% 0.20/0.48          | ~ (l1_pre_topc @ X18))),
% 0.20/0.48      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.48            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48             (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.48         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['9', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.20/0.48          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.48           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.48         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.48           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48              (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.48         <= (~
% 0.20/0.48             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.20/0.48             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.48       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.48       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t65_tops_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( k2_pre_topc @ A @ B ) =
% 0.20/0.48             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X19 : $i, X20 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.48          | ((k2_pre_topc @ X20 @ X19)
% 0.20/0.48              = (k4_subset_1 @ (u1_struct_0 @ X20) @ X19 @ 
% 0.20/0.48                 (k2_tops_1 @ X20 @ X19)))
% 0.20/0.48          | ~ (l1_pre_topc @ X20))),
% 0.20/0.48      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.48            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.48         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48             (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.48         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k7_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.48          | (m1_subset_1 @ (k7_subset_1 @ X7 @ X6 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['31', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.48       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 0.20/0.48          | ((k4_subset_1 @ X10 @ X9 @ X11) = (k2_xboole_0 @ X9 @ X11)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.48            = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.48          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.20/0.48         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.48           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48             (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.48         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.48         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.48  thf(t36_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.20/0.48      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.48  thf(t12_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.48  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.20/0.48         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['42', '47'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.48          = (sk_B)))
% 0.20/0.48         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.48      inference('demod', [status(thm)], ['39', '48'])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.48         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['30', '49'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.48          | ~ (v2_pre_topc @ X16)
% 0.20/0.48          | ((k2_pre_topc @ X16 @ X15) != (X15))
% 0.20/0.48          | (v4_pre_topc @ X15 @ X16)
% 0.20/0.48          | ~ (l1_pre_topc @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v4_pre_topc @ sk_B @ sk_A)
% 0.20/0.48        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.20/0.48        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.48  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.20/0.48         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['50', '56'])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      (((v4_pre_topc @ sk_B @ sk_A))
% 0.20/0.48         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['57'])).
% 0.20/0.48  thf('59', plain,
% 0.20/0.48      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      (~
% 0.20/0.48       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.48          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.48       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.48  thf('61', plain, ($false),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '60'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
