%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OjMeP7Ebbt

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:55 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 240 expanded)
%              Number of leaves         :   33 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          : 1250 (3280 expanded)
%              Number of equality atoms :   85 ( 188 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
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

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('39',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

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

thf('41',plain,
    ( ! [X0: $i] :
        ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
          = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('53',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k2_pre_topc @ X35 @ X34 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X35 ) @ X34 @ ( k2_tops_1 @ X35 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('57',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('58',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','64'])).

thf('66',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','65'])).

thf('67',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','66'])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('69',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_subset_1 @ X19 @ X20 @ ( k3_subset_1 @ X19 @ X20 ) )
        = ( k2_subset_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('70',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('71',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_subset_1 @ X19 @ X20 @ ( k3_subset_1 @ X19 @ X20 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('75',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X30 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('76',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['73','79'])).

thf('81',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OjMeP7Ebbt
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:09:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.59/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.83  % Solved by: fo/fo7.sh
% 0.59/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.83  % done 515 iterations in 0.398s
% 0.59/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.83  % SZS output start Refutation
% 0.59/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.83  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.59/0.83  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.59/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.83  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.59/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.83  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.83  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.59/0.83  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.59/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.83  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.59/0.83  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.59/0.83  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.59/0.83  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.59/0.83  thf(t77_tops_1, conjecture,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83           ( ( v4_pre_topc @ B @ A ) <=>
% 0.59/0.83             ( ( k2_tops_1 @ A @ B ) =
% 0.59/0.83               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.59/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.83    (~( ![A:$i]:
% 0.59/0.83        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.83          ( ![B:$i]:
% 0.59/0.83            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83              ( ( v4_pre_topc @ B @ A ) <=>
% 0.59/0.83                ( ( k2_tops_1 @ A @ B ) =
% 0.59/0.83                  ( k7_subset_1 @
% 0.59/0.83                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.59/0.83    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.59/0.83  thf('0', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83              (k1_tops_1 @ sk_A @ sk_B)))
% 0.59/0.83        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('1', plain,
% 0.59/0.83      (~
% 0.59/0.83       (((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.59/0.83       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.59/0.83      inference('split', [status(esa)], ['0'])).
% 0.59/0.83  thf('2', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83             (k1_tops_1 @ sk_A @ sk_B)))
% 0.59/0.83        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('3', plain,
% 0.59/0.83      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.59/0.83      inference('split', [status(esa)], ['2'])).
% 0.59/0.83  thf('4', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(t52_pre_topc, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( l1_pre_topc @ A ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.59/0.83             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.59/0.83               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.59/0.83  thf('5', plain,
% 0.59/0.83      (![X26 : $i, X27 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.59/0.83          | ~ (v4_pre_topc @ X26 @ X27)
% 0.59/0.83          | ((k2_pre_topc @ X27 @ X26) = (X26))
% 0.59/0.83          | ~ (l1_pre_topc @ X27))),
% 0.59/0.83      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.59/0.83  thf('6', plain,
% 0.59/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.83        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.59/0.83        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.83  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('8', plain,
% 0.59/0.83      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.59/0.83      inference('demod', [status(thm)], ['6', '7'])).
% 0.59/0.83  thf('9', plain,
% 0.59/0.83      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.59/0.83         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['3', '8'])).
% 0.59/0.83  thf('10', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(l78_tops_1, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( l1_pre_topc @ A ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83           ( ( k2_tops_1 @ A @ B ) =
% 0.59/0.83             ( k7_subset_1 @
% 0.59/0.83               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.59/0.83               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.59/0.83  thf('11', plain,
% 0.59/0.83      (![X32 : $i, X33 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.59/0.83          | ((k2_tops_1 @ X33 @ X32)
% 0.59/0.83              = (k7_subset_1 @ (u1_struct_0 @ X33) @ 
% 0.59/0.83                 (k2_pre_topc @ X33 @ X32) @ (k1_tops_1 @ X33 @ X32)))
% 0.59/0.83          | ~ (l1_pre_topc @ X33))),
% 0.59/0.83      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.59/0.83  thf('12', plain,
% 0.59/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.83        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.83               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.83  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('14', plain,
% 0.59/0.83      (((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.59/0.83            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.59/0.83      inference('demod', [status(thm)], ['12', '13'])).
% 0.59/0.83  thf('15', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83             (k1_tops_1 @ sk_A @ sk_B))))
% 0.59/0.83         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['9', '14'])).
% 0.59/0.83  thf('16', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(redefinition_k7_subset_1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.83       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.59/0.83  thf('17', plain,
% 0.59/0.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.59/0.83          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 0.59/0.83      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.59/0.83  thf('18', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.59/0.83           = (k4_xboole_0 @ sk_B @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.83  thf('19', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.59/0.83         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.59/0.83      inference('demod', [status(thm)], ['15', '18'])).
% 0.59/0.83  thf('20', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.59/0.83           = (k4_xboole_0 @ sk_B @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.83  thf('21', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83              (k1_tops_1 @ sk_A @ sk_B))))
% 0.59/0.83         <= (~
% 0.59/0.83             (((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('split', [status(esa)], ['0'])).
% 0.59/0.83  thf('22', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.59/0.83         <= (~
% 0.59/0.83             (((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.83  thf('23', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.59/0.83         <= (~
% 0.59/0.83             (((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.59/0.83             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['19', '22'])).
% 0.59/0.83  thf('24', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.59/0.83       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.59/0.83      inference('simplify', [status(thm)], ['23'])).
% 0.59/0.83  thf('25', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.59/0.83       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.59/0.83      inference('split', [status(esa)], ['2'])).
% 0.59/0.83  thf('26', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.59/0.83           = (k4_xboole_0 @ sk_B @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.83  thf('27', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83             (k1_tops_1 @ sk_A @ sk_B))))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('split', [status(esa)], ['2'])).
% 0.59/0.83  thf('28', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup+', [status(thm)], ['26', '27'])).
% 0.59/0.83  thf(t36_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.83  thf('29', plain,
% 0.59/0.83      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.59/0.83      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.83  thf(t3_subset, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.83  thf('30', plain,
% 0.59/0.83      (![X23 : $i, X25 : $i]:
% 0.59/0.83         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 0.59/0.83      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.83  thf('31', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['29', '30'])).
% 0.59/0.83  thf(d5_subset_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.83       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.59/0.83  thf('32', plain,
% 0.59/0.83      (![X9 : $i, X10 : $i]:
% 0.59/0.83         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.59/0.83          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.59/0.83      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.59/0.83  thf('33', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.59/0.83           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.83  thf('34', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['29', '30'])).
% 0.59/0.83  thf('35', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (m1_subset_1 @ (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.59/0.83          (k1_zfmisc_1 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['33', '34'])).
% 0.59/0.83  thf('36', plain,
% 0.59/0.83      (((m1_subset_1 @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.59/0.83         (k1_zfmisc_1 @ sk_B)))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup+', [status(thm)], ['28', '35'])).
% 0.59/0.83  thf('37', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup+', [status(thm)], ['26', '27'])).
% 0.59/0.83  thf('38', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['29', '30'])).
% 0.59/0.83  thf('39', plain,
% 0.59/0.83      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup+', [status(thm)], ['37', '38'])).
% 0.59/0.83  thf(redefinition_k4_subset_1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.59/0.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.83       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.59/0.83  thf('40', plain,
% 0.59/0.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.59/0.83          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.59/0.83          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.59/0.83      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.59/0.83  thf('41', plain,
% 0.59/0.83      ((![X0 : $i]:
% 0.59/0.83          (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.59/0.83             = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 0.59/0.83           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.83  thf('42', plain,
% 0.59/0.83      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.83          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.59/0.83          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.83             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['36', '41'])).
% 0.59/0.83  thf('43', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup+', [status(thm)], ['26', '27'])).
% 0.59/0.83  thf('44', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.59/0.83           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.83  thf(t39_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.83  thf('45', plain,
% 0.59/0.83      (![X6 : $i, X7 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.59/0.83           = (k2_xboole_0 @ X6 @ X7))),
% 0.59/0.83      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.83  thf('46', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.59/0.83           (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 0.59/0.83           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['44', '45'])).
% 0.59/0.83  thf(commutativity_k2_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.59/0.83  thf('47', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.83  thf('48', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.59/0.83           (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 0.59/0.83           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('demod', [status(thm)], ['46', '47'])).
% 0.59/0.83  thf('49', plain,
% 0.59/0.83      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.83          (k3_subset_1 @ sk_B @ 
% 0.59/0.83           (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.59/0.83          = (k2_xboole_0 @ sk_B @ 
% 0.59/0.83             (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup+', [status(thm)], ['43', '48'])).
% 0.59/0.83  thf('50', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup+', [status(thm)], ['26', '27'])).
% 0.59/0.83  thf('51', plain,
% 0.59/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup+', [status(thm)], ['26', '27'])).
% 0.59/0.83  thf('52', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(t65_tops_1, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( l1_pre_topc @ A ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83           ( ( k2_pre_topc @ A @ B ) =
% 0.59/0.83             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.59/0.83  thf('53', plain,
% 0.59/0.83      (![X34 : $i, X35 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.59/0.83          | ((k2_pre_topc @ X35 @ X34)
% 0.59/0.83              = (k4_subset_1 @ (u1_struct_0 @ X35) @ X34 @ 
% 0.59/0.83                 (k2_tops_1 @ X35 @ X34)))
% 0.59/0.83          | ~ (l1_pre_topc @ X35))),
% 0.59/0.83      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.59/0.83  thf('54', plain,
% 0.59/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.83        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.59/0.83            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['52', '53'])).
% 0.59/0.83  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('56', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(dt_k2_tops_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ( l1_pre_topc @ A ) & 
% 0.59/0.83         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.83       ( m1_subset_1 @
% 0.59/0.83         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.59/0.83  thf('57', plain,
% 0.59/0.83      (![X28 : $i, X29 : $i]:
% 0.59/0.83         (~ (l1_pre_topc @ X28)
% 0.59/0.83          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.59/0.83          | (m1_subset_1 @ (k2_tops_1 @ X28 @ X29) @ 
% 0.59/0.83             (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 0.59/0.83      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.59/0.83  thf('58', plain,
% 0.59/0.83      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.83         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.83        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['56', '57'])).
% 0.59/0.83  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('60', plain,
% 0.59/0.83      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('demod', [status(thm)], ['58', '59'])).
% 0.59/0.83  thf('61', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('62', plain,
% 0.59/0.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.59/0.83          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.59/0.83          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.59/0.83      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.59/0.83  thf('63', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.59/0.83            = (k2_xboole_0 @ sk_B @ X0))
% 0.59/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['61', '62'])).
% 0.59/0.83  thf('64', plain,
% 0.59/0.83      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.59/0.83         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['60', '63'])).
% 0.59/0.83  thf('65', plain,
% 0.59/0.83      (((k2_pre_topc @ sk_A @ sk_B)
% 0.59/0.83         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.59/0.83      inference('demod', [status(thm)], ['54', '55', '64'])).
% 0.59/0.83  thf('66', plain,
% 0.59/0.83      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.83          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.59/0.83          = (k2_pre_topc @ sk_A @ sk_B)))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('demod', [status(thm)], ['49', '50', '51', '65'])).
% 0.59/0.83  thf('67', plain,
% 0.59/0.83      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.83          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.59/0.83          = (k2_pre_topc @ sk_A @ sk_B)))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('demod', [status(thm)], ['42', '66'])).
% 0.59/0.83  thf('68', plain,
% 0.59/0.83      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup+', [status(thm)], ['37', '38'])).
% 0.59/0.83  thf(t25_subset_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.83       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.59/0.83         ( k2_subset_1 @ A ) ) ))).
% 0.59/0.83  thf('69', plain,
% 0.59/0.83      (![X19 : $i, X20 : $i]:
% 0.59/0.83         (((k4_subset_1 @ X19 @ X20 @ (k3_subset_1 @ X19 @ X20))
% 0.59/0.83            = (k2_subset_1 @ X19))
% 0.59/0.83          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.59/0.83  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.59/0.83  thf('70', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.59/0.83      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.59/0.83  thf('71', plain,
% 0.59/0.83      (![X19 : $i, X20 : $i]:
% 0.59/0.83         (((k4_subset_1 @ X19 @ X20 @ (k3_subset_1 @ X19 @ X20)) = (X19))
% 0.59/0.83          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.59/0.83      inference('demod', [status(thm)], ['69', '70'])).
% 0.59/0.83  thf('72', plain,
% 0.59/0.83      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.83          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['68', '71'])).
% 0.59/0.83  thf('73', plain,
% 0.59/0.83      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup+', [status(thm)], ['67', '72'])).
% 0.59/0.83  thf('74', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(fc1_tops_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.59/0.83         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.83       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.59/0.83  thf('75', plain,
% 0.59/0.83      (![X30 : $i, X31 : $i]:
% 0.59/0.83         (~ (l1_pre_topc @ X30)
% 0.59/0.83          | ~ (v2_pre_topc @ X30)
% 0.59/0.83          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.59/0.83          | (v4_pre_topc @ (k2_pre_topc @ X30 @ X31) @ X30))),
% 0.59/0.83      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.59/0.83  thf('76', plain,
% 0.59/0.83      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.59/0.83        | ~ (v2_pre_topc @ sk_A)
% 0.59/0.83        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['74', '75'])).
% 0.59/0.83  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('79', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.59/0.83      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.59/0.83  thf('80', plain,
% 0.59/0.83      (((v4_pre_topc @ sk_B @ sk_A))
% 0.59/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.83      inference('sup+', [status(thm)], ['73', '79'])).
% 0.59/0.83  thf('81', plain,
% 0.59/0.83      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.59/0.83      inference('split', [status(esa)], ['0'])).
% 0.59/0.83  thf('82', plain,
% 0.59/0.83      (~
% 0.59/0.83       (((k2_tops_1 @ sk_A @ sk_B)
% 0.59/0.83          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.59/0.83             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.59/0.83       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['80', '81'])).
% 0.59/0.83  thf('83', plain, ($false),
% 0.59/0.83      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '82'])).
% 0.59/0.83  
% 0.59/0.83  % SZS output end Refutation
% 0.59/0.83  
% 0.59/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
