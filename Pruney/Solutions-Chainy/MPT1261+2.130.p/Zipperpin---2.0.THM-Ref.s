%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8UfQBOJPN3

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 154 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  902 (2088 expanded)
%              Number of equality atoms :   65 ( 123 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_pre_topc @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_tops_1 @ X21 @ X20 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ X20 ) @ ( k1_tops_1 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X23 ) @ X22 @ ( k2_tops_1 @ X23 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
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

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('32',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k4_subset_1 @ X10 @ X9 @ X11 )
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('47',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','52'])).

thf('54',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_pre_topc @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
       != X18 )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8UfQBOJPN3
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:41:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 171 iterations in 0.072s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(t77_tops_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.53             ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.53               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53              ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.53                ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.53                  ( k7_subset_1 @
% 0.20/0.53                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53              (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.53        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (~
% 0.20/0.53       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.53       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53             (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.53        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t52_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.53             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.53               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.53          | ~ (v4_pre_topc @ X18 @ X19)
% 0.20/0.53          | ((k2_pre_topc @ X19 @ X18) = (X18))
% 0.20/0.53          | ~ (l1_pre_topc @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.20/0.53        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.53         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(l78_tops_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.53             ( k7_subset_1 @
% 0.20/0.53               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.20/0.53               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.53          | ((k2_tops_1 @ X21 @ X20)
% 0.20/0.53              = (k7_subset_1 @ (u1_struct_0 @ X21) @ 
% 0.20/0.53                 (k2_pre_topc @ X21 @ X20) @ (k1_tops_1 @ X21 @ X20)))
% 0.20/0.53          | ~ (l1_pre_topc @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.53               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.53            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53             (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['9', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.20/0.53          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.53           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.53           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53              (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.53         <= (~
% 0.20/0.53             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.20/0.53             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.53       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.53       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t65_tops_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( k2_pre_topc @ A @ B ) =
% 0.20/0.53             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.53          | ((k2_pre_topc @ X23 @ X22)
% 0.20/0.53              = (k4_subset_1 @ (u1_struct_0 @ X23) @ X22 @ 
% 0.20/0.53                 (k2_tops_1 @ X23 @ X22)))
% 0.20/0.53          | ~ (l1_pre_topc @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.53            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.53         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.53           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53             (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('36', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.53  thf(t109_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k4_xboole_0 @ X2 @ X4) @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X15 : $i, X17 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.20/0.53          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['33', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.20/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 0.20/0.53          | ((k4_subset_1 @ X10 @ X9 @ X11) = (k2_xboole_0 @ X9 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.53            = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.53          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['41', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf(t36_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.20/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.53  thf(t12_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.53  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['46', '51'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.53          = (sk_B)))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['45', '52'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['30', '53'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.53          | ~ (v2_pre_topc @ X19)
% 0.20/0.53          | ((k2_pre_topc @ X19 @ X18) != (X18))
% 0.20/0.53          | (v4_pre_topc @ X18 @ X19)
% 0.20/0.53          | ~ (l1_pre_topc @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v4_pre_topc @ sk_B @ sk_A)
% 0.20/0.53        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['54', '60'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (((v4_pre_topc @ sk_B @ sk_A))
% 0.20/0.53         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      (~
% 0.20/0.53       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.53          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.53             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.53       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('65', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '64'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
