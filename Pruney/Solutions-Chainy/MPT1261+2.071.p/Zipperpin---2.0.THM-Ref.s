%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZkMn45991h

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 152 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  899 (1982 expanded)
%              Number of equality atoms :   69 ( 122 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

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
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k2_pre_topc @ X35 @ X34 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X35 ) @ X34 @ ( k2_tops_1 @ X35 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('31',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k4_subset_1 @ X21 @ X20 @ X22 )
        = ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','38'])).

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

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('46',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('47',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('48',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('49',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) )
      = ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) @ X10 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) )
      = X6 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X1 ) ) @ X0 ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['45','53'])).

thf('55',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','54'])).

thf('56',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_pre_topc @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
       != X28 )
      | ( v4_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZkMn45991h
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:45:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 137 iterations in 0.067s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(t77_tops_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.52             ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.52               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52              ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.52                ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.52                  ( k7_subset_1 @
% 0.20/0.52                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52              (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.52        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (~
% 0.20/0.52       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.52       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52             (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.52        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t52_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.52             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.52               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.20/0.52          | ~ (v4_pre_topc @ X28 @ X29)
% 0.20/0.52          | ((k2_pre_topc @ X29 @ X28) = (X28))
% 0.20/0.52          | ~ (l1_pre_topc @ X29))),
% 0.20/0.52      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.20/0.52        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.52         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(l78_tops_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.52             ( k7_subset_1 @
% 0.20/0.52               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.20/0.52               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X32 : $i, X33 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.20/0.52          | ((k2_tops_1 @ X33 @ X32)
% 0.20/0.52              = (k7_subset_1 @ (u1_struct_0 @ X33) @ 
% 0.20/0.52                 (k2_pre_topc @ X33 @ X32) @ (k1_tops_1 @ X33 @ X32)))
% 0.20/0.52          | ~ (l1_pre_topc @ X33))),
% 0.20/0.52      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.52               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.52            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52             (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.52         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['9', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.20/0.52          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.52           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.52         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.52           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52              (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.52         <= (~
% 0.20/0.52             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.52         <= (~
% 0.20/0.52             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.52         <= (~
% 0.20/0.52             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.20/0.52             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.52       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.52       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t65_tops_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( k2_pre_topc @ A @ B ) =
% 0.20/0.52             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X34 : $i, X35 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.20/0.52          | ((k2_pre_topc @ X35 @ X34)
% 0.20/0.52              = (k4_subset_1 @ (u1_struct_0 @ X35) @ X34 @ 
% 0.20/0.52                 (k2_tops_1 @ X35 @ X34)))
% 0.20/0.52          | ~ (l1_pre_topc @ X35))),
% 0.20/0.52      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.52            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k2_tops_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @
% 0.20/0.52         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X30 : $i, X31 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X30)
% 0.20/0.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.20/0.52          | (m1_subset_1 @ (k2_tops_1 @ X30 @ X31) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X30))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.20/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 0.20/0.52          | ((k4_subset_1 @ X21 @ X20 @ X22) = (k2_xboole_0 @ X20 @ X22)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.52            = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.52         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.52         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.52           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52             (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.52  thf('43', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.52  thf(t12_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf(t49_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.20/0.52       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.52         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 0.20/0.52           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))
% 0.20/0.52           = (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X8 @ X9)) @ X10))),
% 0.20/0.52      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.20/0.52  thf(t22_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X6 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))) = (X6))),
% 0.20/0.52      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X2 @ 
% 0.20/0.52           (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X1)) @ X0)) = (
% 0.20/0.52           X2))),
% 0.20/0.52      inference('sup+', [status(thm)], ['49', '52'])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['45', '53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.20/0.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['42', '54'])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['39', '55'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.20/0.52          | ~ (v2_pre_topc @ X29)
% 0.20/0.52          | ((k2_pre_topc @ X29 @ X28) != (X28))
% 0.20/0.52          | (v4_pre_topc @ X28 @ X29)
% 0.20/0.52          | ~ (l1_pre_topc @ X29))),
% 0.20/0.52      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v4_pre_topc @ sk_B @ sk_A)
% 0.20/0.52        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.52  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.20/0.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['56', '62'])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (((v4_pre_topc @ sk_B @ sk_A))
% 0.20/0.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['63'])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      (~
% 0.20/0.52       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.52             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.52       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.52  thf('67', plain, ($false),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '66'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
