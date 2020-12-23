%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SGBbTu2QO5

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:43 EST 2020

% Result     : Theorem 3.90s
% Output     : Refutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 716 expanded)
%              Number of leaves         :   37 ( 232 expanded)
%              Depth                    :   16
%              Number of atoms          : 1519 (8814 expanded)
%              Number of equality atoms :  117 ( 672 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v4_pre_topc @ X27 @ X28 )
      | ( ( k2_pre_topc @ X28 @ X27 )
        = X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_tops_1 @ X34 @ X33 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k2_pre_topc @ X34 @ X33 ) @ ( k1_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k6_subset_1 @ X20 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
          = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ X0 ) ) )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ X0 ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['31','40'])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_subset_1 @ X23 @ X24 @ ( k3_subset_1 @ X23 @ X24 ) )
        = ( k2_subset_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('44',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('45',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_subset_1 @ X23 @ X24 @ ( k3_subset_1 @ X23 @ X24 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('48',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','46','47'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('59',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('63',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['55','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('72',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','46','47'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('77',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 @ ( k2_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('81',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('82',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ sk_B )
        = ( k2_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','75','93'])).

thf('95',plain,
    ( ( ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ X0 @ sk_B )
        = ( k2_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','75','93'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('99',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('101',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X31 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('102',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['99','105'])).

thf('107',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('108',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SGBbTu2QO5
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:50:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.90/4.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.90/4.07  % Solved by: fo/fo7.sh
% 3.90/4.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.90/4.07  % done 2907 iterations in 3.616s
% 3.90/4.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.90/4.07  % SZS output start Refutation
% 3.90/4.07  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.90/4.07  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.90/4.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.90/4.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.90/4.07  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.90/4.07  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 3.90/4.07  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 3.90/4.07  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 3.90/4.07  thf(sk_B_type, type, sk_B: $i).
% 3.90/4.07  thf(sk_A_type, type, sk_A: $i).
% 3.90/4.07  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 3.90/4.07  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.90/4.07  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.90/4.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.90/4.07  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.90/4.07  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.90/4.07  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.90/4.07  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.90/4.07  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.90/4.07  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.90/4.07  thf(t77_tops_1, conjecture,
% 3.90/4.07    (![A:$i]:
% 3.90/4.07     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.90/4.07       ( ![B:$i]:
% 3.90/4.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.90/4.07           ( ( v4_pre_topc @ B @ A ) <=>
% 3.90/4.07             ( ( k2_tops_1 @ A @ B ) =
% 3.90/4.07               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 3.90/4.07  thf(zf_stmt_0, negated_conjecture,
% 3.90/4.07    (~( ![A:$i]:
% 3.90/4.07        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.90/4.07          ( ![B:$i]:
% 3.90/4.07            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.90/4.07              ( ( v4_pre_topc @ B @ A ) <=>
% 3.90/4.07                ( ( k2_tops_1 @ A @ B ) =
% 3.90/4.07                  ( k7_subset_1 @
% 3.90/4.07                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 3.90/4.07    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 3.90/4.07  thf('0', plain,
% 3.90/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07              (k1_tops_1 @ sk_A @ sk_B)))
% 3.90/4.07        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 3.90/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.07  thf('1', plain,
% 3.90/4.07      (~
% 3.90/4.07       (((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 3.90/4.07       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 3.90/4.07      inference('split', [status(esa)], ['0'])).
% 3.90/4.07  thf('2', plain,
% 3.90/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07             (k1_tops_1 @ sk_A @ sk_B)))
% 3.90/4.07        | (v4_pre_topc @ sk_B @ sk_A))),
% 3.90/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.07  thf('3', plain,
% 3.90/4.07      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.90/4.07      inference('split', [status(esa)], ['2'])).
% 3.90/4.07  thf('4', plain,
% 3.90/4.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.07  thf(t52_pre_topc, axiom,
% 3.90/4.07    (![A:$i]:
% 3.90/4.07     ( ( l1_pre_topc @ A ) =>
% 3.90/4.07       ( ![B:$i]:
% 3.90/4.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.90/4.07           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 3.90/4.07             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 3.90/4.07               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 3.90/4.07  thf('5', plain,
% 3.90/4.07      (![X27 : $i, X28 : $i]:
% 3.90/4.07         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 3.90/4.07          | ~ (v4_pre_topc @ X27 @ X28)
% 3.90/4.07          | ((k2_pre_topc @ X28 @ X27) = (X27))
% 3.90/4.07          | ~ (l1_pre_topc @ X28))),
% 3.90/4.07      inference('cnf', [status(esa)], [t52_pre_topc])).
% 3.90/4.07  thf('6', plain,
% 3.90/4.07      ((~ (l1_pre_topc @ sk_A)
% 3.90/4.07        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 3.90/4.07        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 3.90/4.07      inference('sup-', [status(thm)], ['4', '5'])).
% 3.90/4.07  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 3.90/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.07  thf('8', plain,
% 3.90/4.07      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 3.90/4.07      inference('demod', [status(thm)], ['6', '7'])).
% 3.90/4.07  thf('9', plain,
% 3.90/4.07      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 3.90/4.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.90/4.07      inference('sup-', [status(thm)], ['3', '8'])).
% 3.90/4.07  thf('10', plain,
% 3.90/4.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.07  thf(l78_tops_1, axiom,
% 3.90/4.07    (![A:$i]:
% 3.90/4.07     ( ( l1_pre_topc @ A ) =>
% 3.90/4.07       ( ![B:$i]:
% 3.90/4.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.90/4.07           ( ( k2_tops_1 @ A @ B ) =
% 3.90/4.07             ( k7_subset_1 @
% 3.90/4.07               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 3.90/4.07               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.90/4.07  thf('11', plain,
% 3.90/4.07      (![X33 : $i, X34 : $i]:
% 3.90/4.07         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 3.90/4.07          | ((k2_tops_1 @ X34 @ X33)
% 3.90/4.07              = (k7_subset_1 @ (u1_struct_0 @ X34) @ 
% 3.90/4.07                 (k2_pre_topc @ X34 @ X33) @ (k1_tops_1 @ X34 @ X33)))
% 3.90/4.07          | ~ (l1_pre_topc @ X34))),
% 3.90/4.07      inference('cnf', [status(esa)], [l78_tops_1])).
% 3.90/4.07  thf('12', plain,
% 3.90/4.07      ((~ (l1_pre_topc @ sk_A)
% 3.90/4.07        | ((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.90/4.07               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 3.90/4.07      inference('sup-', [status(thm)], ['10', '11'])).
% 3.90/4.07  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 3.90/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.07  thf('14', plain,
% 3.90/4.07      (((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.90/4.07            (k1_tops_1 @ sk_A @ sk_B)))),
% 3.90/4.07      inference('demod', [status(thm)], ['12', '13'])).
% 3.90/4.07  thf('15', plain,
% 3.90/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07             (k1_tops_1 @ sk_A @ sk_B))))
% 3.90/4.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.90/4.07      inference('sup+', [status(thm)], ['9', '14'])).
% 3.90/4.07  thf('16', plain,
% 3.90/4.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.07  thf(redefinition_k7_subset_1, axiom,
% 3.90/4.07    (![A:$i,B:$i,C:$i]:
% 3.90/4.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.90/4.07       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 3.90/4.07  thf('17', plain,
% 3.90/4.07      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.90/4.07         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 3.90/4.07          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 3.90/4.07      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.90/4.07  thf(redefinition_k6_subset_1, axiom,
% 3.90/4.07    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 3.90/4.07  thf('18', plain,
% 3.90/4.07      (![X18 : $i, X19 : $i]:
% 3.90/4.07         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 3.90/4.07      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.90/4.07  thf('19', plain,
% 3.90/4.07      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.90/4.07         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 3.90/4.07          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k6_subset_1 @ X20 @ X22)))),
% 3.90/4.07      inference('demod', [status(thm)], ['17', '18'])).
% 3.90/4.07  thf('20', plain,
% 3.90/4.07      (![X0 : $i]:
% 3.90/4.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.90/4.07           = (k6_subset_1 @ sk_B @ X0))),
% 3.90/4.07      inference('sup-', [status(thm)], ['16', '19'])).
% 3.90/4.07  thf('21', plain,
% 3.90/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 3.90/4.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.90/4.07      inference('demod', [status(thm)], ['15', '20'])).
% 3.90/4.07  thf('22', plain,
% 3.90/4.07      (![X0 : $i]:
% 3.90/4.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.90/4.07           = (k6_subset_1 @ sk_B @ X0))),
% 3.90/4.07      inference('sup-', [status(thm)], ['16', '19'])).
% 3.90/4.07  thf('23', plain,
% 3.90/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07              (k1_tops_1 @ sk_A @ sk_B))))
% 3.90/4.07         <= (~
% 3.90/4.07             (((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.07      inference('split', [status(esa)], ['0'])).
% 3.90/4.07  thf('24', plain,
% 3.90/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 3.90/4.07         <= (~
% 3.90/4.07             (((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.07      inference('sup-', [status(thm)], ['22', '23'])).
% 3.90/4.07  thf('25', plain,
% 3.90/4.07      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 3.90/4.07         <= (~
% 3.90/4.07             (((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 3.90/4.07             ((v4_pre_topc @ sk_B @ sk_A)))),
% 3.90/4.07      inference('sup-', [status(thm)], ['21', '24'])).
% 3.90/4.07  thf('26', plain,
% 3.90/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 3.90/4.07       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 3.90/4.07      inference('simplify', [status(thm)], ['25'])).
% 3.90/4.07  thf('27', plain,
% 3.90/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 3.90/4.07       ((v4_pre_topc @ sk_B @ sk_A))),
% 3.90/4.07      inference('split', [status(esa)], ['2'])).
% 3.90/4.07  thf(idempotence_k2_xboole_0, axiom,
% 3.90/4.07    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 3.90/4.07  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 3.90/4.07      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 3.90/4.07  thf('29', plain,
% 3.90/4.07      (![X0 : $i]:
% 3.90/4.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.90/4.07           = (k6_subset_1 @ sk_B @ X0))),
% 3.90/4.07      inference('sup-', [status(thm)], ['16', '19'])).
% 3.90/4.07  thf('30', plain,
% 3.90/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07             (k1_tops_1 @ sk_A @ sk_B))))
% 3.90/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.07      inference('split', [status(esa)], ['2'])).
% 3.90/4.07  thf('31', plain,
% 3.90/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 3.90/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.07      inference('sup+', [status(thm)], ['29', '30'])).
% 3.90/4.07  thf(dt_k6_subset_1, axiom,
% 3.90/4.07    (![A:$i,B:$i]:
% 3.90/4.07     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 3.90/4.07  thf('32', plain,
% 3.90/4.07      (![X13 : $i, X14 : $i]:
% 3.90/4.07         (m1_subset_1 @ (k6_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))),
% 3.90/4.07      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 3.90/4.07  thf(dt_k3_subset_1, axiom,
% 3.90/4.07    (![A:$i,B:$i]:
% 3.90/4.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.90/4.07       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.90/4.07  thf('33', plain,
% 3.90/4.07      (![X11 : $i, X12 : $i]:
% 3.90/4.07         ((m1_subset_1 @ (k3_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 3.90/4.07          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 3.90/4.07      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 3.90/4.07  thf('34', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]:
% 3.90/4.07         (m1_subset_1 @ (k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)) @ 
% 3.90/4.07          (k1_zfmisc_1 @ X0))),
% 3.90/4.07      inference('sup-', [status(thm)], ['32', '33'])).
% 3.90/4.07  thf('35', plain,
% 3.90/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 3.90/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.07      inference('sup+', [status(thm)], ['29', '30'])).
% 3.90/4.07  thf('36', plain,
% 3.90/4.07      (![X13 : $i, X14 : $i]:
% 3.90/4.07         (m1_subset_1 @ (k6_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))),
% 3.90/4.07      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 3.90/4.07  thf('37', plain,
% 3.90/4.07      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 3.90/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.07      inference('sup+', [status(thm)], ['35', '36'])).
% 3.90/4.07  thf(redefinition_k4_subset_1, axiom,
% 3.90/4.07    (![A:$i,B:$i,C:$i]:
% 3.90/4.07     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.90/4.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.90/4.07       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.90/4.07  thf('38', plain,
% 3.90/4.07      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.90/4.07         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 3.90/4.07          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 3.90/4.07          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 3.90/4.07      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.90/4.07  thf('39', plain,
% 3.90/4.07      ((![X0 : $i]:
% 3.90/4.07          (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 3.90/4.07             = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 3.90/4.07           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))))
% 3.90/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.07      inference('sup-', [status(thm)], ['37', '38'])).
% 3.90/4.07  thf('40', plain,
% 3.90/4.07      ((![X0 : $i]:
% 3.90/4.07          ((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.90/4.07            (k3_subset_1 @ sk_B @ (k6_subset_1 @ sk_B @ X0)))
% 3.90/4.07            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.90/4.07               (k3_subset_1 @ sk_B @ (k6_subset_1 @ sk_B @ X0)))))
% 3.90/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.07      inference('sup-', [status(thm)], ['34', '39'])).
% 3.90/4.07  thf('41', plain,
% 3.90/4.07      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.90/4.07          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 3.90/4.07          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.90/4.07             (k3_subset_1 @ sk_B @ 
% 3.90/4.07              (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))))
% 3.90/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.07      inference('sup+', [status(thm)], ['31', '40'])).
% 3.90/4.07  thf('42', plain,
% 3.90/4.07      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 3.90/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.07      inference('sup+', [status(thm)], ['35', '36'])).
% 3.90/4.07  thf(t25_subset_1, axiom,
% 3.90/4.07    (![A:$i,B:$i]:
% 3.90/4.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.90/4.07       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 3.90/4.07         ( k2_subset_1 @ A ) ) ))).
% 3.90/4.07  thf('43', plain,
% 3.90/4.07      (![X23 : $i, X24 : $i]:
% 3.90/4.07         (((k4_subset_1 @ X23 @ X24 @ (k3_subset_1 @ X23 @ X24))
% 3.90/4.07            = (k2_subset_1 @ X23))
% 3.90/4.07          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 3.90/4.07      inference('cnf', [status(esa)], [t25_subset_1])).
% 3.90/4.07  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 3.90/4.07  thf('44', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 3.90/4.07      inference('cnf', [status(esa)], [d4_subset_1])).
% 3.90/4.07  thf('45', plain,
% 3.90/4.07      (![X23 : $i, X24 : $i]:
% 3.90/4.07         (((k4_subset_1 @ X23 @ X24 @ (k3_subset_1 @ X23 @ X24)) = (X23))
% 3.90/4.07          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 3.90/4.07      inference('demod', [status(thm)], ['43', '44'])).
% 3.90/4.07  thf('46', plain,
% 3.90/4.07      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.90/4.07          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 3.90/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.07      inference('sup-', [status(thm)], ['42', '45'])).
% 3.90/4.07  thf('47', plain,
% 3.90/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 3.90/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.07      inference('sup+', [status(thm)], ['29', '30'])).
% 3.90/4.07  thf('48', plain,
% 3.90/4.07      ((((sk_B)
% 3.90/4.07          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.90/4.07             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 3.90/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.07      inference('demod', [status(thm)], ['41', '46', '47'])).
% 3.90/4.07  thf(commutativity_k2_tarski, axiom,
% 3.90/4.07    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.90/4.07  thf('49', plain,
% 3.90/4.07      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 3.90/4.07      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.90/4.07  thf(l51_zfmisc_1, axiom,
% 3.90/4.07    (![A:$i,B:$i]:
% 3.90/4.07     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.90/4.07  thf('50', plain,
% 3.90/4.07      (![X8 : $i, X9 : $i]:
% 3.90/4.07         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 3.90/4.07      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.90/4.07  thf('51', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]:
% 3.90/4.07         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 3.90/4.07      inference('sup+', [status(thm)], ['49', '50'])).
% 3.90/4.07  thf('52', plain,
% 3.90/4.07      (![X8 : $i, X9 : $i]:
% 3.90/4.07         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 3.90/4.07      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.90/4.07  thf('53', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.90/4.07      inference('sup+', [status(thm)], ['51', '52'])).
% 3.90/4.07  thf(t4_xboole_1, axiom,
% 3.90/4.07    (![A:$i,B:$i,C:$i]:
% 3.90/4.07     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 3.90/4.07       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.90/4.07  thf('54', plain,
% 3.90/4.07      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.90/4.07         ((k2_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ X5)
% 3.90/4.07           = (k2_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 3.90/4.07      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.90/4.07  thf('55', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.90/4.07         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 3.90/4.07           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 3.90/4.07      inference('sup+', [status(thm)], ['53', '54'])).
% 3.90/4.07  thf('56', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.90/4.07      inference('sup+', [status(thm)], ['51', '52'])).
% 3.90/4.07  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 3.90/4.07      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 3.90/4.07  thf('58', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.90/4.07      inference('sup+', [status(thm)], ['51', '52'])).
% 3.90/4.07  thf('59', plain,
% 3.90/4.07      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.90/4.07         ((k2_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ X5)
% 3.90/4.07           = (k2_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 3.90/4.07      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.90/4.07  thf('60', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.90/4.07         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 3.90/4.07           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 3.90/4.07      inference('sup+', [status(thm)], ['58', '59'])).
% 3.90/4.07  thf('61', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]:
% 3.90/4.07         ((k2_xboole_0 @ X1 @ X0)
% 3.90/4.07           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 3.90/4.07      inference('sup+', [status(thm)], ['57', '60'])).
% 3.90/4.07  thf('62', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 3.90/4.07      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 3.90/4.07  thf('63', plain,
% 3.90/4.07      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.90/4.07         ((k2_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ X5)
% 3.90/4.07           = (k2_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 3.90/4.07      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.90/4.07  thf('64', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]:
% 3.90/4.07         ((k2_xboole_0 @ X0 @ X1)
% 3.90/4.07           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 3.90/4.07      inference('sup+', [status(thm)], ['62', '63'])).
% 3.90/4.07  thf('65', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]:
% 3.90/4.07         ((k2_xboole_0 @ X1 @ X0)
% 3.90/4.07           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.90/4.07      inference('demod', [status(thm)], ['61', '64'])).
% 3.90/4.07  thf('66', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]:
% 3.90/4.07         ((k2_xboole_0 @ X0 @ X1)
% 3.90/4.07           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.90/4.07      inference('sup+', [status(thm)], ['56', '65'])).
% 3.90/4.07  thf('67', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.90/4.07         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1)
% 3.90/4.07           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 3.90/4.07      inference('sup+', [status(thm)], ['55', '66'])).
% 3.90/4.07  thf('68', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.90/4.07         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 3.90/4.07           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 3.90/4.07      inference('sup+', [status(thm)], ['58', '59'])).
% 3.90/4.07  thf('69', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.90/4.07         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1))
% 3.90/4.07           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 3.90/4.07      inference('demod', [status(thm)], ['67', '68'])).
% 3.90/4.07  thf('70', plain,
% 3.90/4.07      ((![X0 : $i]:
% 3.90/4.07          ((k2_xboole_0 @ X0 @ 
% 3.90/4.07            (k2_xboole_0 @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 3.90/4.07             (k2_tops_1 @ sk_A @ sk_B)))
% 3.90/4.07            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.90/4.08               (k2_xboole_0 @ X0 @ sk_B))))
% 3.90/4.08         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.08                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.08      inference('sup+', [status(thm)], ['48', '69'])).
% 3.90/4.08  thf('71', plain,
% 3.90/4.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.90/4.08      inference('sup+', [status(thm)], ['51', '52'])).
% 3.90/4.08  thf('72', plain,
% 3.90/4.08      ((((sk_B)
% 3.90/4.08          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.90/4.08             (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 3.90/4.08         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.08                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.08      inference('demod', [status(thm)], ['41', '46', '47'])).
% 3.90/4.08  thf('73', plain,
% 3.90/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.90/4.08         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 3.90/4.08           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 3.90/4.08      inference('sup+', [status(thm)], ['58', '59'])).
% 3.90/4.08  thf('74', plain,
% 3.90/4.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.90/4.08      inference('sup+', [status(thm)], ['51', '52'])).
% 3.90/4.08  thf('75', plain,
% 3.90/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.90/4.08         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 3.90/4.08           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.90/4.08      inference('sup+', [status(thm)], ['73', '74'])).
% 3.90/4.08  thf('76', plain,
% 3.90/4.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.08  thf(t65_tops_1, axiom,
% 3.90/4.08    (![A:$i]:
% 3.90/4.08     ( ( l1_pre_topc @ A ) =>
% 3.90/4.08       ( ![B:$i]:
% 3.90/4.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.90/4.08           ( ( k2_pre_topc @ A @ B ) =
% 3.90/4.08             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.90/4.08  thf('77', plain,
% 3.90/4.08      (![X35 : $i, X36 : $i]:
% 3.90/4.08         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 3.90/4.08          | ((k2_pre_topc @ X36 @ X35)
% 3.90/4.08              = (k4_subset_1 @ (u1_struct_0 @ X36) @ X35 @ 
% 3.90/4.08                 (k2_tops_1 @ X36 @ X35)))
% 3.90/4.08          | ~ (l1_pre_topc @ X36))),
% 3.90/4.08      inference('cnf', [status(esa)], [t65_tops_1])).
% 3.90/4.08  thf('78', plain,
% 3.90/4.08      ((~ (l1_pre_topc @ sk_A)
% 3.90/4.08        | ((k2_pre_topc @ sk_A @ sk_B)
% 3.90/4.08            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.08               (k2_tops_1 @ sk_A @ sk_B))))),
% 3.90/4.08      inference('sup-', [status(thm)], ['76', '77'])).
% 3.90/4.08  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 3.90/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.08  thf('80', plain,
% 3.90/4.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.08  thf(dt_k2_tops_1, axiom,
% 3.90/4.08    (![A:$i,B:$i]:
% 3.90/4.08     ( ( ( l1_pre_topc @ A ) & 
% 3.90/4.08         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.90/4.08       ( m1_subset_1 @
% 3.90/4.08         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.90/4.08  thf('81', plain,
% 3.90/4.08      (![X29 : $i, X30 : $i]:
% 3.90/4.08         (~ (l1_pre_topc @ X29)
% 3.90/4.08          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.90/4.08          | (m1_subset_1 @ (k2_tops_1 @ X29 @ X30) @ 
% 3.90/4.08             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 3.90/4.08      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 3.90/4.08  thf('82', plain,
% 3.90/4.08      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.90/4.08         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.90/4.08        | ~ (l1_pre_topc @ sk_A))),
% 3.90/4.08      inference('sup-', [status(thm)], ['80', '81'])).
% 3.90/4.08  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 3.90/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.08  thf('84', plain,
% 3.90/4.08      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.90/4.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.08      inference('demod', [status(thm)], ['82', '83'])).
% 3.90/4.08  thf('85', plain,
% 3.90/4.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.08  thf('86', plain,
% 3.90/4.08      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.90/4.08         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 3.90/4.08          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 3.90/4.08          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 3.90/4.08      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.90/4.08  thf('87', plain,
% 3.90/4.08      (![X0 : $i]:
% 3.90/4.08         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.90/4.08            = (k2_xboole_0 @ sk_B @ X0))
% 3.90/4.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.90/4.08      inference('sup-', [status(thm)], ['85', '86'])).
% 3.90/4.08  thf('88', plain,
% 3.90/4.08      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.90/4.08         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.90/4.08      inference('sup-', [status(thm)], ['84', '87'])).
% 3.90/4.08  thf('89', plain,
% 3.90/4.08      (((k2_pre_topc @ sk_A @ sk_B)
% 3.90/4.08         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.90/4.08      inference('demod', [status(thm)], ['78', '79', '88'])).
% 3.90/4.08  thf('90', plain,
% 3.90/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.90/4.08         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 3.90/4.08           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.90/4.08      inference('sup+', [status(thm)], ['73', '74'])).
% 3.90/4.08  thf('91', plain,
% 3.90/4.08      (![X0 : $i]:
% 3.90/4.08         ((k2_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 3.90/4.08           = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.90/4.08              (k2_xboole_0 @ sk_B @ X0)))),
% 3.90/4.08      inference('sup+', [status(thm)], ['89', '90'])).
% 3.90/4.08  thf('92', plain,
% 3.90/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.90/4.08         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 3.90/4.08           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 3.90/4.08      inference('sup+', [status(thm)], ['53', '54'])).
% 3.90/4.08  thf('93', plain,
% 3.90/4.08      (![X0 : $i]:
% 3.90/4.08         ((k2_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 3.90/4.08           = (k2_xboole_0 @ sk_B @ 
% 3.90/4.08              (k2_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))))),
% 3.90/4.08      inference('demod', [status(thm)], ['91', '92'])).
% 3.90/4.08  thf('94', plain,
% 3.90/4.08      ((![X0 : $i]:
% 3.90/4.08          ((k2_xboole_0 @ X0 @ sk_B)
% 3.90/4.08            = (k2_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_B))))
% 3.90/4.08         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.08                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.08      inference('demod', [status(thm)], ['70', '71', '72', '75', '93'])).
% 3.90/4.08  thf('95', plain,
% 3.90/4.08      ((((k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 3.90/4.08          = (k2_pre_topc @ sk_A @ sk_B)))
% 3.90/4.08         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.08                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.08      inference('sup+', [status(thm)], ['28', '94'])).
% 3.90/4.08  thf('96', plain,
% 3.90/4.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.90/4.08      inference('sup+', [status(thm)], ['51', '52'])).
% 3.90/4.08  thf('97', plain,
% 3.90/4.08      ((![X0 : $i]:
% 3.90/4.08          ((k2_xboole_0 @ X0 @ sk_B)
% 3.90/4.08            = (k2_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ sk_B))))
% 3.90/4.08         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.08                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.08      inference('demod', [status(thm)], ['70', '71', '72', '75', '93'])).
% 3.90/4.08  thf('98', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 3.90/4.08      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 3.90/4.08  thf('99', plain,
% 3.90/4.08      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 3.90/4.08         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.08                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.08      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 3.90/4.08  thf('100', plain,
% 3.90/4.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.90/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.08  thf(fc1_tops_1, axiom,
% 3.90/4.08    (![A:$i,B:$i]:
% 3.90/4.08     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 3.90/4.08         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.90/4.08       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 3.90/4.08  thf('101', plain,
% 3.90/4.08      (![X31 : $i, X32 : $i]:
% 3.90/4.08         (~ (l1_pre_topc @ X31)
% 3.90/4.08          | ~ (v2_pre_topc @ X31)
% 3.90/4.08          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 3.90/4.08          | (v4_pre_topc @ (k2_pre_topc @ X31 @ X32) @ X31))),
% 3.90/4.08      inference('cnf', [status(esa)], [fc1_tops_1])).
% 3.90/4.08  thf('102', plain,
% 3.90/4.08      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 3.90/4.08        | ~ (v2_pre_topc @ sk_A)
% 3.90/4.08        | ~ (l1_pre_topc @ sk_A))),
% 3.90/4.08      inference('sup-', [status(thm)], ['100', '101'])).
% 3.90/4.08  thf('103', plain, ((v2_pre_topc @ sk_A)),
% 3.90/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.08  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 3.90/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.08  thf('105', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 3.90/4.08      inference('demod', [status(thm)], ['102', '103', '104'])).
% 3.90/4.08  thf('106', plain,
% 3.90/4.08      (((v4_pre_topc @ sk_B @ sk_A))
% 3.90/4.08         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.08                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.90/4.08      inference('sup+', [status(thm)], ['99', '105'])).
% 3.90/4.08  thf('107', plain,
% 3.90/4.08      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 3.90/4.08      inference('split', [status(esa)], ['0'])).
% 3.90/4.08  thf('108', plain,
% 3.90/4.08      (~
% 3.90/4.08       (((k2_tops_1 @ sk_A @ sk_B)
% 3.90/4.08          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.90/4.08             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 3.90/4.08       ((v4_pre_topc @ sk_B @ sk_A))),
% 3.90/4.08      inference('sup-', [status(thm)], ['106', '107'])).
% 3.90/4.08  thf('109', plain, ($false),
% 3.90/4.08      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '108'])).
% 3.90/4.08  
% 3.90/4.08  % SZS output end Refutation
% 3.90/4.08  
% 3.90/4.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
