%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2K0TnieY7I

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:55 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 231 expanded)
%              Number of leaves         :   36 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          : 1305 (3152 expanded)
%              Number of equality atoms :   90 ( 184 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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

thf('32',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
          = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('43',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('54',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('55',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('63',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k2_pre_topc @ X35 @ X34 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X35 ) @ X34 @ ( k2_tops_1 @ X35 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','52','67'])).

thf('69',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('71',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = ( k2_subset_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('72',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('73',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['69','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('77',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X30 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('78',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['75','81'])).

thf('83',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2K0TnieY7I
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.58/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.83  % Solved by: fo/fo7.sh
% 0.58/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.83  % done 648 iterations in 0.373s
% 0.58/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.83  % SZS output start Refutation
% 0.58/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.83  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.58/0.83  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.58/0.83  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.58/0.83  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.58/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.83  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.58/0.83  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.58/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.83  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.58/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.83  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.83  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.58/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.83  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.58/0.83  thf(t77_tops_1, conjecture,
% 0.58/0.83    (![A:$i]:
% 0.58/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.83       ( ![B:$i]:
% 0.58/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.83           ( ( v4_pre_topc @ B @ A ) <=>
% 0.58/0.83             ( ( k2_tops_1 @ A @ B ) =
% 0.58/0.83               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.58/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.83    (~( ![A:$i]:
% 0.58/0.83        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.83          ( ![B:$i]:
% 0.58/0.83            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.83              ( ( v4_pre_topc @ B @ A ) <=>
% 0.58/0.83                ( ( k2_tops_1 @ A @ B ) =
% 0.58/0.83                  ( k7_subset_1 @
% 0.58/0.83                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.58/0.83    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.58/0.83  thf('0', plain,
% 0.58/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83              (k1_tops_1 @ sk_A @ sk_B)))
% 0.58/0.83        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('1', plain,
% 0.58/0.83      (~
% 0.58/0.83       (((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.58/0.83       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.83      inference('split', [status(esa)], ['0'])).
% 0.58/0.83  thf('2', plain,
% 0.58/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83             (k1_tops_1 @ sk_A @ sk_B)))
% 0.58/0.83        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('3', plain,
% 0.58/0.83      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.58/0.83      inference('split', [status(esa)], ['2'])).
% 0.58/0.83  thf('4', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(t52_pre_topc, axiom,
% 0.58/0.83    (![A:$i]:
% 0.58/0.83     ( ( l1_pre_topc @ A ) =>
% 0.58/0.83       ( ![B:$i]:
% 0.58/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.83           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.58/0.83             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.58/0.83               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.58/0.83  thf('5', plain,
% 0.58/0.83      (![X26 : $i, X27 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.58/0.83          | ~ (v4_pre_topc @ X26 @ X27)
% 0.58/0.83          | ((k2_pre_topc @ X27 @ X26) = (X26))
% 0.58/0.83          | ~ (l1_pre_topc @ X27))),
% 0.58/0.83      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.58/0.83  thf('6', plain,
% 0.58/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.83        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.58/0.83        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.83      inference('sup-', [status(thm)], ['4', '5'])).
% 0.58/0.83  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('8', plain,
% 0.58/0.83      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.83      inference('demod', [status(thm)], ['6', '7'])).
% 0.58/0.83  thf('9', plain,
% 0.58/0.83      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.58/0.83         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['3', '8'])).
% 0.58/0.83  thf('10', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(l78_tops_1, axiom,
% 0.58/0.83    (![A:$i]:
% 0.58/0.83     ( ( l1_pre_topc @ A ) =>
% 0.58/0.83       ( ![B:$i]:
% 0.58/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.83           ( ( k2_tops_1 @ A @ B ) =
% 0.58/0.83             ( k7_subset_1 @
% 0.58/0.83               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.58/0.83               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.58/0.83  thf('11', plain,
% 0.58/0.83      (![X32 : $i, X33 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.58/0.83          | ((k2_tops_1 @ X33 @ X32)
% 0.58/0.83              = (k7_subset_1 @ (u1_struct_0 @ X33) @ 
% 0.58/0.83                 (k2_pre_topc @ X33 @ X32) @ (k1_tops_1 @ X33 @ X32)))
% 0.58/0.83          | ~ (l1_pre_topc @ X33))),
% 0.58/0.83      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.58/0.83  thf('12', plain,
% 0.58/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.83        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.83               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.83  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('14', plain,
% 0.58/0.83      (((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.58/0.83            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.83      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.83  thf('15', plain,
% 0.58/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83             (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.83         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.58/0.83      inference('sup+', [status(thm)], ['9', '14'])).
% 0.58/0.83  thf('16', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(redefinition_k7_subset_1, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.83       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.58/0.83  thf('17', plain,
% 0.58/0.83      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.58/0.83          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 0.58/0.83      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.58/0.83  thf('18', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.58/0.83           = (k4_xboole_0 @ sk_B @ X0))),
% 0.58/0.83      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.83  thf('19', plain,
% 0.58/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.83         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.58/0.83      inference('demod', [status(thm)], ['15', '18'])).
% 0.58/0.83  thf('20', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.58/0.83           = (k4_xboole_0 @ sk_B @ X0))),
% 0.58/0.83      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.83  thf('21', plain,
% 0.58/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83              (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.83         <= (~
% 0.58/0.83             (((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('split', [status(esa)], ['0'])).
% 0.58/0.83  thf('22', plain,
% 0.58/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.83         <= (~
% 0.58/0.83             (((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.83  thf('23', plain,
% 0.58/0.83      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.58/0.83         <= (~
% 0.58/0.83             (((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.58/0.83             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['19', '22'])).
% 0.58/0.83  thf('24', plain,
% 0.58/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.58/0.83       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.83      inference('simplify', [status(thm)], ['23'])).
% 0.58/0.83  thf('25', plain,
% 0.58/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.58/0.83       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.83      inference('split', [status(esa)], ['2'])).
% 0.58/0.83  thf('26', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.58/0.83           = (k4_xboole_0 @ sk_B @ X0))),
% 0.58/0.83      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.83  thf('27', plain,
% 0.58/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83             (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('split', [status(esa)], ['2'])).
% 0.58/0.83  thf('28', plain,
% 0.58/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup+', [status(thm)], ['26', '27'])).
% 0.58/0.83  thf(t36_xboole_1, axiom,
% 0.58/0.83    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.58/0.83  thf('29', plain,
% 0.58/0.83      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.58/0.83      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.58/0.83  thf(t3_subset, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.83  thf('30', plain,
% 0.58/0.83      (![X23 : $i, X25 : $i]:
% 0.58/0.83         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 0.58/0.83      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.83  thf('31', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.58/0.83      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.83  thf('32', plain,
% 0.58/0.83      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup+', [status(thm)], ['28', '31'])).
% 0.58/0.83  thf(dt_k3_subset_1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.83       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.58/0.83  thf('33', plain,
% 0.58/0.83      (![X13 : $i, X14 : $i]:
% 0.58/0.83         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 0.58/0.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.58/0.83      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.58/0.83  thf('34', plain,
% 0.58/0.83      (((m1_subset_1 @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.58/0.83         (k1_zfmisc_1 @ sk_B)))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.83  thf('35', plain,
% 0.58/0.83      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup+', [status(thm)], ['28', '31'])).
% 0.58/0.83  thf(redefinition_k4_subset_1, axiom,
% 0.58/0.83    (![A:$i,B:$i,C:$i]:
% 0.58/0.83     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.58/0.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.58/0.83       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.58/0.83  thf('36', plain,
% 0.58/0.83      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.58/0.83          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.58/0.83          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.58/0.83      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.58/0.83  thf('37', plain,
% 0.58/0.83      ((![X0 : $i]:
% 0.58/0.83          (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.58/0.83             = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 0.58/0.83           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['35', '36'])).
% 0.58/0.83  thf('38', plain,
% 0.58/0.83      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.58/0.83          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.58/0.83          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.58/0.83             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['34', '37'])).
% 0.58/0.83  thf('39', plain,
% 0.58/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup+', [status(thm)], ['26', '27'])).
% 0.58/0.83  thf(t48_xboole_1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.83  thf('40', plain,
% 0.58/0.83      (![X8 : $i, X9 : $i]:
% 0.58/0.83         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.58/0.83           = (k3_xboole_0 @ X8 @ X9))),
% 0.58/0.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.83  thf('41', plain,
% 0.58/0.83      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.58/0.83          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup+', [status(thm)], ['39', '40'])).
% 0.58/0.83  thf(t39_xboole_1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.83  thf('42', plain,
% 0.58/0.83      (![X6 : $i, X7 : $i]:
% 0.58/0.83         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.58/0.83           = (k2_xboole_0 @ X6 @ X7))),
% 0.58/0.83      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.58/0.83  thf('43', plain,
% 0.58/0.83      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.58/0.83          (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.58/0.83          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup+', [status(thm)], ['41', '42'])).
% 0.58/0.83  thf(commutativity_k2_xboole_0, axiom,
% 0.58/0.83    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.58/0.83  thf('44', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.83  thf('45', plain,
% 0.58/0.83      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.58/0.83          (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.58/0.83          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('demod', [status(thm)], ['43', '44'])).
% 0.58/0.83  thf('46', plain,
% 0.58/0.83      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup+', [status(thm)], ['26', '27'])).
% 0.58/0.83  thf('47', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.58/0.83      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.83  thf(d5_subset_1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.83       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.58/0.83  thf('48', plain,
% 0.58/0.83      (![X11 : $i, X12 : $i]:
% 0.58/0.83         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.58/0.83          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.58/0.83      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.58/0.83  thf('49', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.58/0.83           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['47', '48'])).
% 0.58/0.83  thf('50', plain,
% 0.58/0.83      (![X8 : $i, X9 : $i]:
% 0.58/0.83         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.58/0.83           = (k3_xboole_0 @ X8 @ X9))),
% 0.58/0.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.83  thf('51', plain,
% 0.58/0.83      (![X0 : $i, X1 : $i]:
% 0.58/0.83         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.58/0.83           = (k3_xboole_0 @ X1 @ X0))),
% 0.58/0.83      inference('sup+', [status(thm)], ['49', '50'])).
% 0.58/0.83  thf('52', plain,
% 0.58/0.83      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.58/0.83          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup+', [status(thm)], ['46', '51'])).
% 0.58/0.83  thf('53', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(dt_k2_tops_1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( ( l1_pre_topc @ A ) & 
% 0.58/0.83         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.83       ( m1_subset_1 @
% 0.58/0.83         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.58/0.83  thf('54', plain,
% 0.58/0.83      (![X28 : $i, X29 : $i]:
% 0.58/0.83         (~ (l1_pre_topc @ X28)
% 0.58/0.83          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.58/0.83          | (m1_subset_1 @ (k2_tops_1 @ X28 @ X29) @ 
% 0.58/0.83             (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 0.58/0.83      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.58/0.83  thf('55', plain,
% 0.58/0.83      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.58/0.83         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.83        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.83      inference('sup-', [status(thm)], ['53', '54'])).
% 0.58/0.83  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('57', plain,
% 0.58/0.83      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.58/0.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.83      inference('demod', [status(thm)], ['55', '56'])).
% 0.58/0.83  thf('58', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('59', plain,
% 0.58/0.83      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.58/0.83          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.58/0.83          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.58/0.83      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.58/0.83  thf('60', plain,
% 0.58/0.83      (![X0 : $i]:
% 0.58/0.83         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.58/0.83            = (k2_xboole_0 @ sk_B @ X0))
% 0.58/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['58', '59'])).
% 0.58/0.83  thf('61', plain,
% 0.58/0.83      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.58/0.83         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.83      inference('sup-', [status(thm)], ['57', '60'])).
% 0.58/0.83  thf('62', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(t65_tops_1, axiom,
% 0.58/0.83    (![A:$i]:
% 0.58/0.83     ( ( l1_pre_topc @ A ) =>
% 0.58/0.83       ( ![B:$i]:
% 0.58/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.83           ( ( k2_pre_topc @ A @ B ) =
% 0.58/0.83             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.58/0.83  thf('63', plain,
% 0.58/0.83      (![X34 : $i, X35 : $i]:
% 0.58/0.83         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.58/0.83          | ((k2_pre_topc @ X35 @ X34)
% 0.58/0.83              = (k4_subset_1 @ (u1_struct_0 @ X35) @ X34 @ 
% 0.58/0.83                 (k2_tops_1 @ X35 @ X34)))
% 0.58/0.83          | ~ (l1_pre_topc @ X35))),
% 0.58/0.83      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.58/0.83  thf('64', plain,
% 0.58/0.83      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.83        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.58/0.83            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['62', '63'])).
% 0.58/0.83  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('66', plain,
% 0.58/0.83      (((k2_pre_topc @ sk_A @ sk_B)
% 0.58/0.83         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.83      inference('demod', [status(thm)], ['64', '65'])).
% 0.58/0.83  thf('67', plain,
% 0.58/0.83      (((k2_pre_topc @ sk_A @ sk_B)
% 0.58/0.83         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.83      inference('sup+', [status(thm)], ['61', '66'])).
% 0.58/0.83  thf('68', plain,
% 0.58/0.83      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.58/0.83          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.58/0.83          = (k2_pre_topc @ sk_A @ sk_B)))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('demod', [status(thm)], ['45', '52', '67'])).
% 0.58/0.83  thf('69', plain,
% 0.58/0.83      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.58/0.83          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.58/0.83          = (k2_pre_topc @ sk_A @ sk_B)))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('demod', [status(thm)], ['38', '68'])).
% 0.58/0.83  thf('70', plain,
% 0.58/0.83      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup+', [status(thm)], ['28', '31'])).
% 0.58/0.83  thf(t25_subset_1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.83       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.58/0.83         ( k2_subset_1 @ A ) ) ))).
% 0.58/0.83  thf('71', plain,
% 0.58/0.83      (![X21 : $i, X22 : $i]:
% 0.58/0.83         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22))
% 0.58/0.83            = (k2_subset_1 @ X21))
% 0.58/0.83          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.58/0.83      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.58/0.83  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.58/0.83  thf('72', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 0.58/0.83      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.58/0.83  thf('73', plain,
% 0.58/0.83      (![X21 : $i, X22 : $i]:
% 0.58/0.83         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22)) = (X21))
% 0.58/0.83          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.58/0.83      inference('demod', [status(thm)], ['71', '72'])).
% 0.58/0.83  thf('74', plain,
% 0.58/0.83      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.58/0.83          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup-', [status(thm)], ['70', '73'])).
% 0.58/0.83  thf('75', plain,
% 0.58/0.83      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup+', [status(thm)], ['69', '74'])).
% 0.58/0.83  thf('76', plain,
% 0.58/0.83      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf(fc1_tops_1, axiom,
% 0.58/0.83    (![A:$i,B:$i]:
% 0.58/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.58/0.83         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.83       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.58/0.83  thf('77', plain,
% 0.58/0.83      (![X30 : $i, X31 : $i]:
% 0.58/0.83         (~ (l1_pre_topc @ X30)
% 0.58/0.83          | ~ (v2_pre_topc @ X30)
% 0.58/0.83          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.58/0.83          | (v4_pre_topc @ (k2_pre_topc @ X30 @ X31) @ X30))),
% 0.58/0.83      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.58/0.83  thf('78', plain,
% 0.58/0.83      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.58/0.83        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.83        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.83      inference('sup-', [status(thm)], ['76', '77'])).
% 0.58/0.83  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.83  thf('81', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.58/0.83      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.58/0.83  thf('82', plain,
% 0.58/0.83      (((v4_pre_topc @ sk_B @ sk_A))
% 0.58/0.83         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.83      inference('sup+', [status(thm)], ['75', '81'])).
% 0.58/0.83  thf('83', plain,
% 0.58/0.83      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.58/0.83      inference('split', [status(esa)], ['0'])).
% 0.58/0.83  thf('84', plain,
% 0.58/0.83      (~
% 0.58/0.83       (((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.83          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.83             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.58/0.83       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.83      inference('sup-', [status(thm)], ['82', '83'])).
% 0.58/0.83  thf('85', plain, ($false),
% 0.58/0.83      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '84'])).
% 0.58/0.83  
% 0.58/0.83  % SZS output end Refutation
% 0.58/0.83  
% 0.58/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
