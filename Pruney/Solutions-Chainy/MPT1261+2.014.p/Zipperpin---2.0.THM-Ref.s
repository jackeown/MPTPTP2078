%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XShGLJvxU3

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:38 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 241 expanded)
%              Number of leaves         :   41 (  84 expanded)
%              Depth                    :   16
%              Number of atoms          : 1325 (3009 expanded)
%              Number of equality atoms :  110 ( 206 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
        = X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k2_tops_1 @ X35 @ X34 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X35 ) @ ( k2_pre_topc @ X35 @ X34 ) @ ( k1_tops_1 @ X35 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k1_tops_1 @ X39 @ X38 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X39 ) @ X38 @ ( k2_tops_1 @ X39 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('38',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('40',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_tarski @ X17 @ X16 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('55',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','58'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('60',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('61',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('62',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('63',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','74'])).

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
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k2_pre_topc @ X37 @ X36 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 @ ( k2_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) ) ) ),
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

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('86',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k4_subset_1 @ X21 @ X20 @ X22 )
        = ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
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

thf('90',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['75','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('92',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X32 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('93',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['90','96'])).

thf('98',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('99',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XShGLJvxU3
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:44:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 783 iterations in 0.209s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.66  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.66  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.45/0.66  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.45/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.66  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.45/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(t77_tops_1, conjecture,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( v4_pre_topc @ B @ A ) <=>
% 0.45/0.66             ( ( k2_tops_1 @ A @ B ) =
% 0.45/0.66               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i]:
% 0.45/0.66        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.66          ( ![B:$i]:
% 0.45/0.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66              ( ( v4_pre_topc @ B @ A ) <=>
% 0.45/0.66                ( ( k2_tops_1 @ A @ B ) =
% 0.45/0.66                  ( k7_subset_1 @
% 0.45/0.66                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66              (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.66        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (~
% 0.45/0.66       (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.66       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66             (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.66        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('split', [status(esa)], ['2'])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t52_pre_topc, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.45/0.66             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.45/0.66               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X28 : $i, X29 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.45/0.66          | ~ (v4_pre_topc @ X28 @ X29)
% 0.45/0.66          | ((k2_pre_topc @ X29 @ X28) = (X28))
% 0.45/0.66          | ~ (l1_pre_topc @ X29))),
% 0.45/0.66      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.45/0.66        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.45/0.66         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['3', '8'])).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(l78_tops_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( k2_tops_1 @ A @ B ) =
% 0.45/0.66             ( k7_subset_1 @
% 0.45/0.66               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.45/0.66               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X34 : $i, X35 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.45/0.66          | ((k2_tops_1 @ X35 @ X34)
% 0.45/0.66              = (k7_subset_1 @ (u1_struct_0 @ X35) @ 
% 0.45/0.66                 (k2_pre_topc @ X35 @ X34) @ (k1_tops_1 @ X35 @ X34)))
% 0.45/0.66          | ~ (l1_pre_topc @ X35))),
% 0.45/0.66      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.66               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.45/0.66            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66             (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['9', '14'])).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(redefinition_k7_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.66       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.45/0.66          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.66           = (k4_xboole_0 @ sk_B @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['15', '18'])).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.66           = (k4_xboole_0 @ sk_B @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66              (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= (~
% 0.45/0.66             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= (~
% 0.45/0.66             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.66         <= (~
% 0.45/0.66             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.45/0.66             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['19', '22'])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.66       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.66      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.66       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.66      inference('split', [status(esa)], ['2'])).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.66           = (k4_xboole_0 @ sk_B @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66             (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('split', [status(esa)], ['2'])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.66  thf(t48_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (![X12 : $i, X13 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.45/0.66           = (k3_xboole_0 @ X12 @ X13))),
% 0.45/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.66          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['28', '29'])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      (![X12 : $i, X13 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.45/0.66           = (k3_xboole_0 @ X12 @ X13))),
% 0.45/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      ((((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.66          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['30', '31'])).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t74_tops_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( k1_tops_1 @ A @ B ) =
% 0.45/0.66             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (![X38 : $i, X39 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.45/0.66          | ((k1_tops_1 @ X39 @ X38)
% 0.45/0.66              = (k7_subset_1 @ (u1_struct_0 @ X39) @ X38 @ 
% 0.45/0.66                 (k2_tops_1 @ X39 @ X38)))
% 0.45/0.66          | ~ (l1_pre_topc @ X39))),
% 0.45/0.66      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.66            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.66  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.66           = (k4_xboole_0 @ sk_B @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      (((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.66         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.66          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['28', '29'])).
% 0.45/0.66  thf('40', plain,
% 0.45/0.66      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['38', '39'])).
% 0.45/0.66  thf('41', plain,
% 0.45/0.66      ((((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.66          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('demod', [status(thm)], ['32', '40'])).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('demod', [status(thm)], ['41', '42'])).
% 0.45/0.66  thf(commutativity_k2_tarski, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      (![X16 : $i, X17 : $i]:
% 0.45/0.66         ((k2_tarski @ X17 @ X16) = (k2_tarski @ X16 @ X17))),
% 0.45/0.66      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.45/0.66  thf(t12_setfam_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.66  thf('45', plain,
% 0.45/0.66      (![X26 : $i, X27 : $i]:
% 0.45/0.66         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.45/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.66      inference('sup+', [status(thm)], ['44', '45'])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      (![X26 : $i, X27 : $i]:
% 0.45/0.66         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.45/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.66      inference('sup+', [status(thm)], ['46', '47'])).
% 0.45/0.66  thf(t100_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X4 @ X5)
% 0.45/0.66           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['48', '49'])).
% 0.45/0.66  thf('51', plain,
% 0.45/0.66      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.45/0.66          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.66             (k2_tops_1 @ sk_A @ sk_B))))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['43', '50'])).
% 0.45/0.66  thf(idempotence_k3_xboole_0, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.66  thf('52', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.66      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.66  thf('53', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X4 @ X5)
% 0.45/0.66           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.66  thf('54', plain,
% 0.45/0.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['52', '53'])).
% 0.45/0.66  thf(t1_boole, axiom,
% 0.45/0.66    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.66  thf('55', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.45/0.66      inference('cnf', [status(esa)], [t1_boole])).
% 0.45/0.66  thf(t46_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.45/0.66  thf('56', plain,
% 0.45/0.66      (![X10 : $i, X11 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.45/0.66  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('58', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['54', '57'])).
% 0.45/0.66  thf('59', plain,
% 0.45/0.66      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('demod', [status(thm)], ['51', '58'])).
% 0.45/0.66  thf(t98_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.66  thf('60', plain,
% 0.45/0.66      (![X14 : $i, X15 : $i]:
% 0.45/0.66         ((k2_xboole_0 @ X14 @ X15)
% 0.45/0.66           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.66  thf('61', plain,
% 0.45/0.66      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.66          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['59', '60'])).
% 0.45/0.66  thf(t17_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.45/0.66  thf('62', plain,
% 0.45/0.66      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.45/0.66      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.45/0.66  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.66  thf('63', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.66  thf(d10_xboole_0, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.66  thf('64', plain,
% 0.45/0.66      (![X1 : $i, X3 : $i]:
% 0.45/0.66         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('65', plain,
% 0.45/0.66      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['63', '64'])).
% 0.45/0.66  thf('66', plain,
% 0.45/0.66      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['62', '65'])).
% 0.45/0.66  thf('67', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X4 @ X5)
% 0.45/0.66           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.66  thf('68', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.66           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['66', '67'])).
% 0.45/0.66  thf('69', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['54', '57'])).
% 0.45/0.66  thf('70', plain,
% 0.45/0.66      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['68', '69'])).
% 0.45/0.66  thf('71', plain,
% 0.45/0.66      (![X14 : $i, X15 : $i]:
% 0.45/0.66         ((k2_xboole_0 @ X14 @ X15)
% 0.45/0.66           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.66  thf('72', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['70', '71'])).
% 0.45/0.66  thf('73', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.45/0.66      inference('cnf', [status(esa)], [t1_boole])).
% 0.45/0.66  thf('74', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['72', '73'])).
% 0.45/0.66  thf('75', plain,
% 0.45/0.66      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('demod', [status(thm)], ['61', '74'])).
% 0.45/0.66  thf('76', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t65_tops_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( k2_pre_topc @ A @ B ) =
% 0.45/0.66             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.66  thf('77', plain,
% 0.45/0.66      (![X36 : $i, X37 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.45/0.66          | ((k2_pre_topc @ X37 @ X36)
% 0.45/0.66              = (k4_subset_1 @ (u1_struct_0 @ X37) @ X36 @ 
% 0.45/0.66                 (k2_tops_1 @ X37 @ X36)))
% 0.45/0.66          | ~ (l1_pre_topc @ X37))),
% 0.45/0.66      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.45/0.66  thf('78', plain,
% 0.45/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.66        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.45/0.66            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['76', '77'])).
% 0.45/0.66  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('80', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(dt_k2_tops_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( l1_pre_topc @ A ) & 
% 0.45/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.66       ( m1_subset_1 @
% 0.45/0.66         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.66  thf('81', plain,
% 0.45/0.66      (![X30 : $i, X31 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ X30)
% 0.45/0.66          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.45/0.66          | (m1_subset_1 @ (k2_tops_1 @ X30 @ X31) @ 
% 0.45/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X30))))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.45/0.66  thf('82', plain,
% 0.45/0.66      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['80', '81'])).
% 0.45/0.66  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('84', plain,
% 0.45/0.66      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['82', '83'])).
% 0.45/0.66  thf('85', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(redefinition_k4_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.45/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.66       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.45/0.66  thf('86', plain,
% 0.45/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.45/0.66          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 0.45/0.66          | ((k4_subset_1 @ X21 @ X20 @ X22) = (k2_xboole_0 @ X20 @ X22)))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.45/0.66  thf('87', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.66            = (k2_xboole_0 @ sk_B @ X0))
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['85', '86'])).
% 0.45/0.66  thf('88', plain,
% 0.45/0.66      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.66         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['84', '87'])).
% 0.45/0.66  thf('89', plain,
% 0.45/0.66      (((k2_pre_topc @ sk_A @ sk_B)
% 0.45/0.66         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['78', '79', '88'])).
% 0.45/0.66  thf('90', plain,
% 0.45/0.66      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['75', '89'])).
% 0.45/0.66  thf('91', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(fc1_tops_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.45/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.66       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.45/0.66  thf('92', plain,
% 0.45/0.66      (![X32 : $i, X33 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ X32)
% 0.45/0.66          | ~ (v2_pre_topc @ X32)
% 0.45/0.66          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.45/0.66          | (v4_pre_topc @ (k2_pre_topc @ X32 @ X33) @ X32))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.45/0.66  thf('93', plain,
% 0.45/0.66      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.45/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['91', '92'])).
% 0.45/0.66  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('96', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.45/0.66      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.45/0.66  thf('97', plain,
% 0.45/0.66      (((v4_pre_topc @ sk_B @ sk_A))
% 0.45/0.66         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['90', '96'])).
% 0.45/0.66  thf('98', plain,
% 0.45/0.66      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('99', plain,
% 0.45/0.66      (~
% 0.45/0.66       (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.66          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.66       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['97', '98'])).
% 0.45/0.66  thf('100', plain, ($false),
% 0.45/0.66      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '99'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
