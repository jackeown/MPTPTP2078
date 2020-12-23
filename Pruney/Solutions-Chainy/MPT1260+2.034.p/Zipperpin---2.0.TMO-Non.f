%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rm86zylgZ4

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:27 EST 2020

% Result     : Timeout 57.45s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  212 ( 517 expanded)
%              Number of leaves         :   50 ( 177 expanded)
%              Depth                    :   16
%              Number of atoms          : 1900 (5503 expanded)
%              Number of equality atoms :  136 ( 405 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['6','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X31 @ X30 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X24 @ X25 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('18',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('21',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X60 ) @ X59 ) @ X60 )
      | ( v4_pre_topc @ X59 @ X60 )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('25',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X40 @ ( k3_subset_1 @ X40 @ X39 ) )
        = X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('26',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('30',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,
    ( ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','32'])).

thf('34',plain,
    ( ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','33'])).

thf('35',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('37',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

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

thf('38',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( v4_pre_topc @ X49 @ X50 )
      | ( ( k2_pre_topc @ X50 @ X49 )
        = X49 )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('43',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('44',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('45',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( ( k1_tops_1 @ X52 @ X51 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X52 ) @ ( k2_pre_topc @ X52 @ ( k3_subset_1 @ ( u1_struct_0 @ X52 ) @ X51 ) ) ) )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('52',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['46','52'])).

thf('54',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['26','31'])).

thf('55',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('57',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( ( k2_tops_1 @ X58 @ X57 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X58 ) @ ( k2_pre_topc @ X58 @ X57 ) @ ( k1_tops_1 @ X58 @ X57 ) ) )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('67',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( l1_pre_topc @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X53 @ X54 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('72',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X37 @ X36 @ X38 ) @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('76',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ( ( k2_pre_topc @ X64 @ X63 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X64 ) @ X63 @ ( k2_tops_1 @ X64 @ X63 ) ) )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','79'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('81',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( ( k7_subset_1 @ X42 @ X41 @ X43 )
        = ( k4_xboole_0 @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('84',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('85',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('86',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('87',plain,(
    ! [X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('90',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('91',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('92',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('93',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('94',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('95',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('99',plain,(
    ! [X23: $i] :
      ( ( k3_xboole_0 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('100',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('101',plain,(
    ! [X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('104',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('105',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('108',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','111'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('113',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('114',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('115',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('116',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) ) )
      = ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) ) @ X29 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X1 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['112','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('121',plain,(
    ! [X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('122',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X15 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('123',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('124',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('125',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('126',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X17 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 ) ) ) ),
    inference(demod,[status(thm)],['122','123','124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['121','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('129',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X31 @ X30 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['120','130'])).

thf('132',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) ) )
      = ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) ) @ X29 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('133',plain,(
    ! [X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    ! [X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('136',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['119','134','139'])).

thf('141',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['84','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('143',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X66 ) ) )
      | ( ( k1_tops_1 @ X66 @ X65 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X66 ) @ X65 @ ( k2_tops_1 @ X66 @ X65 ) ) )
      | ~ ( l1_pre_topc @ X66 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('144',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( ( k7_subset_1 @ X42 @ X41 @ X43 )
        = ( k4_xboole_0 @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['144','145','148'])).

thf('150',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['141','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('152',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( l1_pre_topc @ X55 )
      | ~ ( v2_pre_topc @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X55 @ X56 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('153',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['150','156'])).

thf('158',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('159',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','64','65','159'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rm86zylgZ4
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:00:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 57.45/57.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 57.45/57.68  % Solved by: fo/fo7.sh
% 57.45/57.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 57.45/57.68  % done 15447 iterations in 57.233s
% 57.45/57.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 57.45/57.68  % SZS output start Refutation
% 57.45/57.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 57.45/57.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 57.45/57.68  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 57.45/57.68  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 57.45/57.68  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 57.45/57.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 57.45/57.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 57.45/57.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 57.45/57.68  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 57.45/57.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 57.45/57.68  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 57.45/57.68  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 57.45/57.68  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 57.45/57.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 57.45/57.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 57.45/57.68  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 57.45/57.68  thf(sk_B_type, type, sk_B: $i).
% 57.45/57.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 57.45/57.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 57.45/57.68  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 57.45/57.68  thf(sk_A_type, type, sk_A: $i).
% 57.45/57.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 57.45/57.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 57.45/57.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 57.45/57.68  thf(t76_tops_1, conjecture,
% 57.45/57.68    (![A:$i]:
% 57.45/57.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 57.45/57.68       ( ![B:$i]:
% 57.45/57.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 57.45/57.68           ( ( v3_pre_topc @ B @ A ) <=>
% 57.45/57.68             ( ( k2_tops_1 @ A @ B ) =
% 57.45/57.68               ( k7_subset_1 @
% 57.45/57.68                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 57.45/57.68  thf(zf_stmt_0, negated_conjecture,
% 57.45/57.68    (~( ![A:$i]:
% 57.45/57.68        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 57.45/57.68          ( ![B:$i]:
% 57.45/57.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 57.45/57.68              ( ( v3_pre_topc @ B @ A ) <=>
% 57.45/57.68                ( ( k2_tops_1 @ A @ B ) =
% 57.45/57.68                  ( k7_subset_1 @
% 57.45/57.68                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 57.45/57.68    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 57.45/57.68  thf('0', plain,
% 57.45/57.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 57.45/57.68        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf('1', plain,
% 57.45/57.68      (~
% 57.45/57.68       (((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 57.45/57.68       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 57.45/57.68      inference('split', [status(esa)], ['0'])).
% 57.45/57.68  thf('2', plain,
% 57.45/57.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 57.45/57.68        | (v3_pre_topc @ sk_B @ sk_A))),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf('3', plain,
% 57.45/57.68      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 57.45/57.68      inference('split', [status(esa)], ['2'])).
% 57.45/57.68  thf('4', plain,
% 57.45/57.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf(t3_subset, axiom,
% 57.45/57.68    (![A:$i,B:$i]:
% 57.45/57.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 57.45/57.68  thf('5', plain,
% 57.45/57.68      (![X46 : $i, X47 : $i]:
% 57.45/57.68         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 57.45/57.68      inference('cnf', [status(esa)], [t3_subset])).
% 57.45/57.68  thf('6', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 57.45/57.68      inference('sup-', [status(thm)], ['4', '5'])).
% 57.45/57.68  thf(t28_xboole_1, axiom,
% 57.45/57.68    (![A:$i,B:$i]:
% 57.45/57.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 57.45/57.68  thf('7', plain,
% 57.45/57.68      (![X21 : $i, X22 : $i]:
% 57.45/57.68         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 57.45/57.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 57.45/57.68  thf(t12_setfam_1, axiom,
% 57.45/57.68    (![A:$i,B:$i]:
% 57.45/57.68     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 57.45/57.68  thf('8', plain,
% 57.45/57.68      (![X44 : $i, X45 : $i]:
% 57.45/57.68         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 57.45/57.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 57.45/57.68  thf('9', plain,
% 57.45/57.68      (![X21 : $i, X22 : $i]:
% 57.45/57.68         (((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (X21))
% 57.45/57.68          | ~ (r1_tarski @ X21 @ X22))),
% 57.45/57.68      inference('demod', [status(thm)], ['7', '8'])).
% 57.45/57.68  thf('10', plain,
% 57.45/57.68      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 57.45/57.68      inference('sup-', [status(thm)], ['6', '9'])).
% 57.45/57.68  thf(commutativity_k2_tarski, axiom,
% 57.45/57.68    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 57.45/57.68  thf('11', plain,
% 57.45/57.68      (![X30 : $i, X31 : $i]:
% 57.45/57.68         ((k2_tarski @ X31 @ X30) = (k2_tarski @ X30 @ X31))),
% 57.45/57.68      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 57.45/57.68  thf(t100_xboole_1, axiom,
% 57.45/57.68    (![A:$i,B:$i]:
% 57.45/57.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 57.45/57.68  thf('12', plain,
% 57.45/57.68      (![X13 : $i, X14 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X13 @ X14)
% 57.45/57.68           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 57.45/57.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 57.45/57.68  thf('13', plain,
% 57.45/57.68      (![X44 : $i, X45 : $i]:
% 57.45/57.68         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 57.45/57.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 57.45/57.68  thf('14', plain,
% 57.45/57.68      (![X13 : $i, X14 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X13 @ X14)
% 57.45/57.68           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 57.45/57.68      inference('demod', [status(thm)], ['12', '13'])).
% 57.45/57.68  thf('15', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X0 @ X1)
% 57.45/57.68           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 57.45/57.68      inference('sup+', [status(thm)], ['11', '14'])).
% 57.45/57.68  thf('16', plain,
% 57.45/57.68      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 57.45/57.68         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 57.45/57.68      inference('sup+', [status(thm)], ['10', '15'])).
% 57.45/57.68  thf(t36_xboole_1, axiom,
% 57.45/57.68    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 57.45/57.68  thf('17', plain,
% 57.45/57.68      (![X24 : $i, X25 : $i]: (r1_tarski @ (k4_xboole_0 @ X24 @ X25) @ X24)),
% 57.45/57.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 57.45/57.68  thf('18', plain,
% 57.45/57.68      (![X46 : $i, X48 : $i]:
% 57.45/57.68         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 57.45/57.68      inference('cnf', [status(esa)], [t3_subset])).
% 57.45/57.68  thf('19', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 57.45/57.68      inference('sup-', [status(thm)], ['17', '18'])).
% 57.45/57.68  thf('20', plain,
% 57.45/57.68      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 57.45/57.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('sup+', [status(thm)], ['16', '19'])).
% 57.45/57.68  thf(t29_tops_1, axiom,
% 57.45/57.68    (![A:$i]:
% 57.45/57.68     ( ( l1_pre_topc @ A ) =>
% 57.45/57.68       ( ![B:$i]:
% 57.45/57.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 57.45/57.68           ( ( v4_pre_topc @ B @ A ) <=>
% 57.45/57.68             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 57.45/57.68  thf('21', plain,
% 57.45/57.68      (![X59 : $i, X60 : $i]:
% 57.45/57.68         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 57.45/57.68          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X60) @ X59) @ X60)
% 57.45/57.68          | (v4_pre_topc @ X59 @ X60)
% 57.45/57.68          | ~ (l1_pre_topc @ X60))),
% 57.45/57.68      inference('cnf', [status(esa)], [t29_tops_1])).
% 57.45/57.68  thf('22', plain,
% 57.45/57.68      ((~ (l1_pre_topc @ sk_A)
% 57.45/57.68        | (v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 57.45/57.68        | ~ (v3_pre_topc @ 
% 57.45/57.68             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68              (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 57.45/57.68             sk_A))),
% 57.45/57.68      inference('sup-', [status(thm)], ['20', '21'])).
% 57.45/57.68  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf('24', plain,
% 57.45/57.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf(involutiveness_k3_subset_1, axiom,
% 57.45/57.68    (![A:$i,B:$i]:
% 57.45/57.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 57.45/57.68       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 57.45/57.68  thf('25', plain,
% 57.45/57.68      (![X39 : $i, X40 : $i]:
% 57.45/57.68         (((k3_subset_1 @ X40 @ (k3_subset_1 @ X40 @ X39)) = (X39))
% 57.45/57.68          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 57.45/57.68      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 57.45/57.68  thf('26', plain,
% 57.45/57.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 57.45/57.68      inference('sup-', [status(thm)], ['24', '25'])).
% 57.45/57.68  thf('27', plain,
% 57.45/57.68      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 57.45/57.68         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 57.45/57.68      inference('sup+', [status(thm)], ['10', '15'])).
% 57.45/57.68  thf('28', plain,
% 57.45/57.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf(d5_subset_1, axiom,
% 57.45/57.68    (![A:$i,B:$i]:
% 57.45/57.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 57.45/57.68       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 57.45/57.68  thf('29', plain,
% 57.45/57.68      (![X32 : $i, X33 : $i]:
% 57.45/57.68         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 57.45/57.68          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 57.45/57.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 57.45/57.68  thf('30', plain,
% 57.45/57.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 57.45/57.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 57.45/57.68      inference('sup-', [status(thm)], ['28', '29'])).
% 57.45/57.68  thf('31', plain,
% 57.45/57.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 57.45/57.68         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 57.45/57.68      inference('sup+', [status(thm)], ['27', '30'])).
% 57.45/57.68  thf('32', plain,
% 57.45/57.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 57.45/57.68      inference('demod', [status(thm)], ['26', '31'])).
% 57.45/57.68  thf('33', plain,
% 57.45/57.68      (((v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 57.45/57.68        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 57.45/57.68      inference('demod', [status(thm)], ['22', '23', '32'])).
% 57.45/57.68  thf('34', plain,
% 57.45/57.68      (((v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 57.45/57.68         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 57.45/57.68      inference('sup-', [status(thm)], ['3', '33'])).
% 57.45/57.68  thf('35', plain,
% 57.45/57.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 57.45/57.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 57.45/57.68      inference('sup-', [status(thm)], ['28', '29'])).
% 57.45/57.68  thf('36', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 57.45/57.68      inference('sup-', [status(thm)], ['17', '18'])).
% 57.45/57.68  thf('37', plain,
% 57.45/57.68      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 57.45/57.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('sup+', [status(thm)], ['35', '36'])).
% 57.45/57.68  thf(t52_pre_topc, axiom,
% 57.45/57.68    (![A:$i]:
% 57.45/57.68     ( ( l1_pre_topc @ A ) =>
% 57.45/57.68       ( ![B:$i]:
% 57.45/57.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 57.45/57.68           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 57.45/57.68             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 57.45/57.68               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 57.45/57.68  thf('38', plain,
% 57.45/57.68      (![X49 : $i, X50 : $i]:
% 57.45/57.68         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 57.45/57.68          | ~ (v4_pre_topc @ X49 @ X50)
% 57.45/57.68          | ((k2_pre_topc @ X50 @ X49) = (X49))
% 57.45/57.68          | ~ (l1_pre_topc @ X50))),
% 57.45/57.68      inference('cnf', [status(esa)], [t52_pre_topc])).
% 57.45/57.68  thf('39', plain,
% 57.45/57.68      ((~ (l1_pre_topc @ sk_A)
% 57.45/57.68        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 57.45/57.68            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 57.45/57.68        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 57.45/57.68      inference('sup-', [status(thm)], ['37', '38'])).
% 57.45/57.68  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf('41', plain,
% 57.45/57.68      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 57.45/57.68          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 57.45/57.68        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 57.45/57.68      inference('demod', [status(thm)], ['39', '40'])).
% 57.45/57.68  thf('42', plain,
% 57.45/57.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 57.45/57.68         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 57.45/57.68      inference('sup+', [status(thm)], ['27', '30'])).
% 57.45/57.68  thf('43', plain,
% 57.45/57.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 57.45/57.68         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 57.45/57.68      inference('sup+', [status(thm)], ['27', '30'])).
% 57.45/57.68  thf('44', plain,
% 57.45/57.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 57.45/57.68         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 57.45/57.68      inference('sup+', [status(thm)], ['27', '30'])).
% 57.45/57.68  thf('45', plain,
% 57.45/57.68      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 57.45/57.68          = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 57.45/57.68        | ~ (v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 57.45/57.68      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 57.45/57.68  thf('46', plain,
% 57.45/57.68      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 57.45/57.68          = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 57.45/57.68         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 57.45/57.68      inference('sup-', [status(thm)], ['34', '45'])).
% 57.45/57.68  thf('47', plain,
% 57.45/57.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf(d1_tops_1, axiom,
% 57.45/57.68    (![A:$i]:
% 57.45/57.68     ( ( l1_pre_topc @ A ) =>
% 57.45/57.68       ( ![B:$i]:
% 57.45/57.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 57.45/57.68           ( ( k1_tops_1 @ A @ B ) =
% 57.45/57.68             ( k3_subset_1 @
% 57.45/57.68               ( u1_struct_0 @ A ) @ 
% 57.45/57.68               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 57.45/57.68  thf('48', plain,
% 57.45/57.68      (![X51 : $i, X52 : $i]:
% 57.45/57.68         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 57.45/57.68          | ((k1_tops_1 @ X52 @ X51)
% 57.45/57.68              = (k3_subset_1 @ (u1_struct_0 @ X52) @ 
% 57.45/57.68                 (k2_pre_topc @ X52 @ (k3_subset_1 @ (u1_struct_0 @ X52) @ X51))))
% 57.45/57.68          | ~ (l1_pre_topc @ X52))),
% 57.45/57.68      inference('cnf', [status(esa)], [d1_tops_1])).
% 57.45/57.68  thf('49', plain,
% 57.45/57.68      ((~ (l1_pre_topc @ sk_A)
% 57.45/57.68        | ((k1_tops_1 @ sk_A @ sk_B)
% 57.45/57.68            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68               (k2_pre_topc @ sk_A @ 
% 57.45/57.68                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 57.45/57.68      inference('sup-', [status(thm)], ['47', '48'])).
% 57.45/57.68  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf('51', plain,
% 57.45/57.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 57.45/57.68         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 57.45/57.68      inference('sup+', [status(thm)], ['27', '30'])).
% 57.45/57.68  thf('52', plain,
% 57.45/57.68      (((k1_tops_1 @ sk_A @ sk_B)
% 57.45/57.68         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 57.45/57.68      inference('demod', [status(thm)], ['49', '50', '51'])).
% 57.45/57.68  thf('53', plain,
% 57.45/57.68      ((((k1_tops_1 @ sk_A @ sk_B)
% 57.45/57.68          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 57.45/57.68         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 57.45/57.68      inference('sup+', [status(thm)], ['46', '52'])).
% 57.45/57.68  thf('54', plain,
% 57.45/57.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 57.45/57.68      inference('demod', [status(thm)], ['26', '31'])).
% 57.45/57.68  thf('55', plain,
% 57.45/57.68      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 57.45/57.68         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 57.45/57.68      inference('sup+', [status(thm)], ['53', '54'])).
% 57.45/57.68  thf('56', plain,
% 57.45/57.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf(l78_tops_1, axiom,
% 57.45/57.68    (![A:$i]:
% 57.45/57.68     ( ( l1_pre_topc @ A ) =>
% 57.45/57.68       ( ![B:$i]:
% 57.45/57.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 57.45/57.68           ( ( k2_tops_1 @ A @ B ) =
% 57.45/57.68             ( k7_subset_1 @
% 57.45/57.68               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 57.45/57.68               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 57.45/57.68  thf('57', plain,
% 57.45/57.68      (![X57 : $i, X58 : $i]:
% 57.45/57.68         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 57.45/57.68          | ((k2_tops_1 @ X58 @ X57)
% 57.45/57.68              = (k7_subset_1 @ (u1_struct_0 @ X58) @ 
% 57.45/57.68                 (k2_pre_topc @ X58 @ X57) @ (k1_tops_1 @ X58 @ X57)))
% 57.45/57.68          | ~ (l1_pre_topc @ X58))),
% 57.45/57.68      inference('cnf', [status(esa)], [l78_tops_1])).
% 57.45/57.68  thf('58', plain,
% 57.45/57.68      ((~ (l1_pre_topc @ sk_A)
% 57.45/57.68        | ((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 57.45/57.68      inference('sup-', [status(thm)], ['56', '57'])).
% 57.45/57.68  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf('60', plain,
% 57.45/57.68      (((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 57.45/57.68            (k1_tops_1 @ sk_A @ sk_B)))),
% 57.45/57.68      inference('demod', [status(thm)], ['58', '59'])).
% 57.45/57.68  thf('61', plain,
% 57.45/57.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 57.45/57.68         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 57.45/57.68      inference('sup+', [status(thm)], ['55', '60'])).
% 57.45/57.68  thf('62', plain,
% 57.45/57.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 57.45/57.68         <= (~
% 57.45/57.68             (((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 57.45/57.68      inference('split', [status(esa)], ['0'])).
% 57.45/57.68  thf('63', plain,
% 57.45/57.68      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 57.45/57.68         <= (~
% 57.45/57.68             (((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 57.45/57.68             ((v3_pre_topc @ sk_B @ sk_A)))),
% 57.45/57.68      inference('sup-', [status(thm)], ['61', '62'])).
% 57.45/57.68  thf('64', plain,
% 57.45/57.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 57.45/57.68       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 57.45/57.68      inference('simplify', [status(thm)], ['63'])).
% 57.45/57.68  thf('65', plain,
% 57.45/57.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 57.45/57.68       ((v3_pre_topc @ sk_B @ sk_A))),
% 57.45/57.68      inference('split', [status(esa)], ['2'])).
% 57.45/57.68  thf('66', plain,
% 57.45/57.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf(dt_k2_tops_1, axiom,
% 57.45/57.68    (![A:$i,B:$i]:
% 57.45/57.68     ( ( ( l1_pre_topc @ A ) & 
% 57.45/57.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 57.45/57.68       ( m1_subset_1 @
% 57.45/57.68         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 57.45/57.68  thf('67', plain,
% 57.45/57.68      (![X53 : $i, X54 : $i]:
% 57.45/57.68         (~ (l1_pre_topc @ X53)
% 57.45/57.68          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 57.45/57.68          | (m1_subset_1 @ (k2_tops_1 @ X53 @ X54) @ 
% 57.45/57.68             (k1_zfmisc_1 @ (u1_struct_0 @ X53))))),
% 57.45/57.68      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 57.45/57.68  thf('68', plain,
% 57.45/57.68      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 57.45/57.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 57.45/57.68        | ~ (l1_pre_topc @ sk_A))),
% 57.45/57.68      inference('sup-', [status(thm)], ['66', '67'])).
% 57.45/57.68  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf('70', plain,
% 57.45/57.68      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 57.45/57.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('demod', [status(thm)], ['68', '69'])).
% 57.45/57.68  thf('71', plain,
% 57.45/57.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf(dt_k4_subset_1, axiom,
% 57.45/57.68    (![A:$i,B:$i,C:$i]:
% 57.45/57.68     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 57.45/57.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 57.45/57.68       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 57.45/57.68  thf('72', plain,
% 57.45/57.68      (![X36 : $i, X37 : $i, X38 : $i]:
% 57.45/57.68         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 57.45/57.68          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37))
% 57.45/57.68          | (m1_subset_1 @ (k4_subset_1 @ X37 @ X36 @ X38) @ 
% 57.45/57.68             (k1_zfmisc_1 @ X37)))),
% 57.45/57.68      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 57.45/57.68  thf('73', plain,
% 57.45/57.68      (![X0 : $i]:
% 57.45/57.68         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 57.45/57.68           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 57.45/57.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 57.45/57.68      inference('sup-', [status(thm)], ['71', '72'])).
% 57.45/57.68  thf('74', plain,
% 57.45/57.68      ((m1_subset_1 @ 
% 57.45/57.68        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 57.45/57.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('sup-', [status(thm)], ['70', '73'])).
% 57.45/57.68  thf('75', plain,
% 57.45/57.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf(t65_tops_1, axiom,
% 57.45/57.68    (![A:$i]:
% 57.45/57.68     ( ( l1_pre_topc @ A ) =>
% 57.45/57.68       ( ![B:$i]:
% 57.45/57.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 57.45/57.68           ( ( k2_pre_topc @ A @ B ) =
% 57.45/57.68             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 57.45/57.68  thf('76', plain,
% 57.45/57.68      (![X63 : $i, X64 : $i]:
% 57.45/57.68         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 57.45/57.68          | ((k2_pre_topc @ X64 @ X63)
% 57.45/57.68              = (k4_subset_1 @ (u1_struct_0 @ X64) @ X63 @ 
% 57.45/57.68                 (k2_tops_1 @ X64 @ X63)))
% 57.45/57.68          | ~ (l1_pre_topc @ X64))),
% 57.45/57.68      inference('cnf', [status(esa)], [t65_tops_1])).
% 57.45/57.68  thf('77', plain,
% 57.45/57.68      ((~ (l1_pre_topc @ sk_A)
% 57.45/57.68        | ((k2_pre_topc @ sk_A @ sk_B)
% 57.45/57.68            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 57.45/57.68               (k2_tops_1 @ sk_A @ sk_B))))),
% 57.45/57.68      inference('sup-', [status(thm)], ['75', '76'])).
% 57.45/57.68  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf('79', plain,
% 57.45/57.68      (((k2_pre_topc @ sk_A @ sk_B)
% 57.45/57.68         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 57.45/57.68            (k2_tops_1 @ sk_A @ sk_B)))),
% 57.45/57.68      inference('demod', [status(thm)], ['77', '78'])).
% 57.45/57.68  thf('80', plain,
% 57.45/57.68      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 57.45/57.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('demod', [status(thm)], ['74', '79'])).
% 57.45/57.68  thf(redefinition_k7_subset_1, axiom,
% 57.45/57.68    (![A:$i,B:$i,C:$i]:
% 57.45/57.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 57.45/57.68       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 57.45/57.68  thf('81', plain,
% 57.45/57.68      (![X41 : $i, X42 : $i, X43 : $i]:
% 57.45/57.68         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 57.45/57.68          | ((k7_subset_1 @ X42 @ X41 @ X43) = (k4_xboole_0 @ X41 @ X43)))),
% 57.45/57.68      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 57.45/57.68  thf('82', plain,
% 57.45/57.68      (![X0 : $i]:
% 57.45/57.68         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 57.45/57.68           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 57.45/57.68      inference('sup-', [status(thm)], ['80', '81'])).
% 57.45/57.68  thf('83', plain,
% 57.45/57.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 57.45/57.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 57.45/57.68      inference('split', [status(esa)], ['2'])).
% 57.45/57.68  thf('84', plain,
% 57.45/57.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 57.45/57.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 57.45/57.68      inference('sup+', [status(thm)], ['82', '83'])).
% 57.45/57.68  thf(idempotence_k3_xboole_0, axiom,
% 57.45/57.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 57.45/57.68  thf('85', plain, (![X12 : $i]: ((k3_xboole_0 @ X12 @ X12) = (X12))),
% 57.45/57.68      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 57.45/57.68  thf('86', plain,
% 57.45/57.68      (![X44 : $i, X45 : $i]:
% 57.45/57.68         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 57.45/57.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 57.45/57.68  thf('87', plain,
% 57.45/57.68      (![X12 : $i]: ((k1_setfam_1 @ (k2_tarski @ X12 @ X12)) = (X12))),
% 57.45/57.68      inference('demod', [status(thm)], ['85', '86'])).
% 57.45/57.68  thf('88', plain,
% 57.45/57.68      (![X13 : $i, X14 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X13 @ X14)
% 57.45/57.68           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 57.45/57.68      inference('demod', [status(thm)], ['12', '13'])).
% 57.45/57.68  thf('89', plain,
% 57.45/57.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 57.45/57.68      inference('sup+', [status(thm)], ['87', '88'])).
% 57.45/57.68  thf(d4_xboole_0, axiom,
% 57.45/57.68    (![A:$i,B:$i,C:$i]:
% 57.45/57.68     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 57.45/57.68       ( ![D:$i]:
% 57.45/57.68         ( ( r2_hidden @ D @ C ) <=>
% 57.45/57.68           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 57.45/57.68  thf('90', plain,
% 57.45/57.68      (![X1 : $i, X2 : $i, X5 : $i]:
% 57.45/57.68         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 57.45/57.68          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 57.45/57.68          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 57.45/57.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 57.45/57.68  thf('91', plain,
% 57.45/57.68      (![X44 : $i, X45 : $i]:
% 57.45/57.68         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 57.45/57.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 57.45/57.68  thf('92', plain,
% 57.45/57.68      (![X1 : $i, X2 : $i, X5 : $i]:
% 57.45/57.68         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 57.45/57.68          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 57.45/57.68          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 57.45/57.68      inference('demod', [status(thm)], ['90', '91'])).
% 57.45/57.68  thf(t3_boole, axiom,
% 57.45/57.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 57.45/57.68  thf('93', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 57.45/57.68      inference('cnf', [status(esa)], [t3_boole])).
% 57.45/57.68  thf(d5_xboole_0, axiom,
% 57.45/57.68    (![A:$i,B:$i,C:$i]:
% 57.45/57.68     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 57.45/57.68       ( ![D:$i]:
% 57.45/57.68         ( ( r2_hidden @ D @ C ) <=>
% 57.45/57.68           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 57.45/57.68  thf('94', plain,
% 57.45/57.68      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 57.45/57.68         (~ (r2_hidden @ X10 @ X9)
% 57.45/57.68          | ~ (r2_hidden @ X10 @ X8)
% 57.45/57.68          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 57.45/57.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 57.45/57.68  thf('95', plain,
% 57.45/57.68      (![X7 : $i, X8 : $i, X10 : $i]:
% 57.45/57.68         (~ (r2_hidden @ X10 @ X8)
% 57.45/57.68          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 57.45/57.68      inference('simplify', [status(thm)], ['94'])).
% 57.45/57.68  thf('96', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 57.45/57.68      inference('sup-', [status(thm)], ['93', '95'])).
% 57.45/57.68  thf('97', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 57.45/57.68      inference('condensation', [status(thm)], ['96'])).
% 57.45/57.68  thf('98', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 57.45/57.68          | ((X1) = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0))))),
% 57.45/57.68      inference('sup-', [status(thm)], ['92', '97'])).
% 57.45/57.68  thf(t2_boole, axiom,
% 57.45/57.68    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 57.45/57.68  thf('99', plain,
% 57.45/57.68      (![X23 : $i]: ((k3_xboole_0 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 57.45/57.68      inference('cnf', [status(esa)], [t2_boole])).
% 57.45/57.68  thf('100', plain,
% 57.45/57.68      (![X44 : $i, X45 : $i]:
% 57.45/57.68         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 57.45/57.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 57.45/57.68  thf('101', plain,
% 57.45/57.68      (![X23 : $i]:
% 57.45/57.68         ((k1_setfam_1 @ (k2_tarski @ X23 @ k1_xboole_0)) = (k1_xboole_0))),
% 57.45/57.68      inference('demod', [status(thm)], ['99', '100'])).
% 57.45/57.68  thf('102', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 57.45/57.68          | ((X1) = (k1_xboole_0)))),
% 57.45/57.68      inference('demod', [status(thm)], ['98', '101'])).
% 57.45/57.68  thf('103', plain,
% 57.45/57.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 57.45/57.68      inference('sup+', [status(thm)], ['87', '88'])).
% 57.45/57.68  thf('104', plain,
% 57.45/57.68      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 57.45/57.68         (~ (r2_hidden @ X10 @ X9)
% 57.45/57.68          | (r2_hidden @ X10 @ X7)
% 57.45/57.68          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 57.45/57.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 57.45/57.68  thf('105', plain,
% 57.45/57.68      (![X7 : $i, X8 : $i, X10 : $i]:
% 57.45/57.68         ((r2_hidden @ X10 @ X7)
% 57.45/57.68          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 57.45/57.68      inference('simplify', [status(thm)], ['104'])).
% 57.45/57.68  thf('106', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 57.45/57.68      inference('sup-', [status(thm)], ['103', '105'])).
% 57.45/57.68  thf('107', plain,
% 57.45/57.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 57.45/57.68      inference('sup+', [status(thm)], ['87', '88'])).
% 57.45/57.68  thf('108', plain,
% 57.45/57.68      (![X7 : $i, X8 : $i, X10 : $i]:
% 57.45/57.68         (~ (r2_hidden @ X10 @ X8)
% 57.45/57.68          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 57.45/57.68      inference('simplify', [status(thm)], ['94'])).
% 57.45/57.68  thf('109', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 57.45/57.68          | ~ (r2_hidden @ X1 @ X0))),
% 57.45/57.68      inference('sup-', [status(thm)], ['107', '108'])).
% 57.45/57.68  thf('110', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 57.45/57.68      inference('clc', [status(thm)], ['106', '109'])).
% 57.45/57.68  thf('111', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 57.45/57.68      inference('sup-', [status(thm)], ['102', '110'])).
% 57.45/57.68  thf('112', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 57.45/57.68      inference('demod', [status(thm)], ['89', '111'])).
% 57.45/57.68  thf(t49_xboole_1, axiom,
% 57.45/57.68    (![A:$i,B:$i,C:$i]:
% 57.45/57.68     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 57.45/57.68       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 57.45/57.68  thf('113', plain,
% 57.45/57.68      (![X27 : $i, X28 : $i, X29 : $i]:
% 57.45/57.68         ((k3_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X29))
% 57.45/57.68           = (k4_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ X29))),
% 57.45/57.68      inference('cnf', [status(esa)], [t49_xboole_1])).
% 57.45/57.68  thf('114', plain,
% 57.45/57.68      (![X44 : $i, X45 : $i]:
% 57.45/57.68         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 57.45/57.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 57.45/57.68  thf('115', plain,
% 57.45/57.68      (![X44 : $i, X45 : $i]:
% 57.45/57.68         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 57.45/57.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 57.45/57.68  thf('116', plain,
% 57.45/57.68      (![X27 : $i, X28 : $i, X29 : $i]:
% 57.45/57.68         ((k1_setfam_1 @ (k2_tarski @ X27 @ (k4_xboole_0 @ X28 @ X29)))
% 57.45/57.68           = (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X27 @ X28)) @ X29))),
% 57.45/57.68      inference('demod', [status(thm)], ['113', '114', '115'])).
% 57.45/57.68  thf('117', plain,
% 57.45/57.68      (![X13 : $i, X14 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X13 @ X14)
% 57.45/57.68           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 57.45/57.68      inference('demod', [status(thm)], ['12', '13'])).
% 57.45/57.68  thf('118', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 57.45/57.68           = (k5_xboole_0 @ X2 @ 
% 57.45/57.68              (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X1)) @ X0)))),
% 57.45/57.68      inference('sup+', [status(thm)], ['116', '117'])).
% 57.45/57.68  thf('119', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X1 @ 
% 57.45/57.68           (k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 57.45/57.68           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 57.45/57.68      inference('sup+', [status(thm)], ['112', '118'])).
% 57.45/57.68  thf('120', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X0 @ X1)
% 57.45/57.68           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 57.45/57.68      inference('sup+', [status(thm)], ['11', '14'])).
% 57.45/57.68  thf('121', plain,
% 57.45/57.68      (![X12 : $i]: ((k1_setfam_1 @ (k2_tarski @ X12 @ X12)) = (X12))),
% 57.45/57.68      inference('demod', [status(thm)], ['85', '86'])).
% 57.45/57.68  thf(t112_xboole_1, axiom,
% 57.45/57.68    (![A:$i,B:$i,C:$i]:
% 57.45/57.68     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 57.45/57.68       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 57.45/57.68  thf('122', plain,
% 57.45/57.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 57.45/57.68         ((k5_xboole_0 @ (k3_xboole_0 @ X15 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 57.45/57.68           = (k3_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17))),
% 57.45/57.68      inference('cnf', [status(esa)], [t112_xboole_1])).
% 57.45/57.68  thf('123', plain,
% 57.45/57.68      (![X44 : $i, X45 : $i]:
% 57.45/57.68         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 57.45/57.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 57.45/57.68  thf('124', plain,
% 57.45/57.68      (![X44 : $i, X45 : $i]:
% 57.45/57.68         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 57.45/57.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 57.45/57.68  thf('125', plain,
% 57.45/57.68      (![X44 : $i, X45 : $i]:
% 57.45/57.68         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 57.45/57.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 57.45/57.68  thf('126', plain,
% 57.45/57.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 57.45/57.68         ((k5_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X17)) @ 
% 57.45/57.68           (k1_setfam_1 @ (k2_tarski @ X16 @ X17)))
% 57.45/57.68           = (k1_setfam_1 @ (k2_tarski @ (k5_xboole_0 @ X15 @ X16) @ X17)))),
% 57.45/57.68      inference('demod', [status(thm)], ['122', '123', '124', '125'])).
% 57.45/57.68  thf('127', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         ((k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 57.45/57.68           = (k1_setfam_1 @ (k2_tarski @ (k5_xboole_0 @ X0 @ X1) @ X0)))),
% 57.45/57.68      inference('sup+', [status(thm)], ['121', '126'])).
% 57.45/57.68  thf('128', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X0 @ X1)
% 57.45/57.68           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 57.45/57.68      inference('sup+', [status(thm)], ['11', '14'])).
% 57.45/57.68  thf('129', plain,
% 57.45/57.68      (![X30 : $i, X31 : $i]:
% 57.45/57.68         ((k2_tarski @ X31 @ X30) = (k2_tarski @ X30 @ X31))),
% 57.45/57.68      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 57.45/57.68  thf('130', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X0 @ X1)
% 57.45/57.68           = (k1_setfam_1 @ (k2_tarski @ X0 @ (k5_xboole_0 @ X0 @ X1))))),
% 57.45/57.68      inference('demod', [status(thm)], ['127', '128', '129'])).
% 57.45/57.68  thf('131', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 57.45/57.68           = (k1_setfam_1 @ (k2_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 57.45/57.68      inference('sup+', [status(thm)], ['120', '130'])).
% 57.45/57.68  thf('132', plain,
% 57.45/57.68      (![X27 : $i, X28 : $i, X29 : $i]:
% 57.45/57.68         ((k1_setfam_1 @ (k2_tarski @ X27 @ (k4_xboole_0 @ X28 @ X29)))
% 57.45/57.68           = (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X27 @ X28)) @ X29))),
% 57.45/57.68      inference('demod', [status(thm)], ['113', '114', '115'])).
% 57.45/57.68  thf('133', plain,
% 57.45/57.68      (![X12 : $i]: ((k1_setfam_1 @ (k2_tarski @ X12 @ X12)) = (X12))),
% 57.45/57.68      inference('demod', [status(thm)], ['85', '86'])).
% 57.45/57.68  thf('134', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 57.45/57.68           = (k4_xboole_0 @ X1 @ X0))),
% 57.45/57.68      inference('demod', [status(thm)], ['131', '132', '133'])).
% 57.45/57.68  thf('135', plain,
% 57.45/57.68      (![X23 : $i]:
% 57.45/57.68         ((k1_setfam_1 @ (k2_tarski @ X23 @ k1_xboole_0)) = (k1_xboole_0))),
% 57.45/57.68      inference('demod', [status(thm)], ['99', '100'])).
% 57.45/57.68  thf('136', plain,
% 57.45/57.68      (![X13 : $i, X14 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X13 @ X14)
% 57.45/57.68           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 57.45/57.68      inference('demod', [status(thm)], ['12', '13'])).
% 57.45/57.68  thf('137', plain,
% 57.45/57.68      (![X0 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 57.45/57.68      inference('sup+', [status(thm)], ['135', '136'])).
% 57.45/57.68  thf('138', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 57.45/57.68      inference('cnf', [status(esa)], [t3_boole])).
% 57.45/57.68  thf('139', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 57.45/57.68      inference('sup+', [status(thm)], ['137', '138'])).
% 57.45/57.68  thf('140', plain,
% 57.45/57.68      (![X0 : $i, X1 : $i]:
% 57.45/57.68         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (X1))),
% 57.45/57.68      inference('demod', [status(thm)], ['119', '134', '139'])).
% 57.45/57.68  thf('141', plain,
% 57.45/57.68      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 57.45/57.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 57.45/57.68      inference('sup+', [status(thm)], ['84', '140'])).
% 57.45/57.68  thf('142', plain,
% 57.45/57.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf(t74_tops_1, axiom,
% 57.45/57.68    (![A:$i]:
% 57.45/57.68     ( ( l1_pre_topc @ A ) =>
% 57.45/57.68       ( ![B:$i]:
% 57.45/57.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 57.45/57.68           ( ( k1_tops_1 @ A @ B ) =
% 57.45/57.68             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 57.45/57.68  thf('143', plain,
% 57.45/57.68      (![X65 : $i, X66 : $i]:
% 57.45/57.68         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (u1_struct_0 @ X66)))
% 57.45/57.68          | ((k1_tops_1 @ X66 @ X65)
% 57.45/57.68              = (k7_subset_1 @ (u1_struct_0 @ X66) @ X65 @ 
% 57.45/57.68                 (k2_tops_1 @ X66 @ X65)))
% 57.45/57.68          | ~ (l1_pre_topc @ X66))),
% 57.45/57.68      inference('cnf', [status(esa)], [t74_tops_1])).
% 57.45/57.68  thf('144', plain,
% 57.45/57.68      ((~ (l1_pre_topc @ sk_A)
% 57.45/57.68        | ((k1_tops_1 @ sk_A @ sk_B)
% 57.45/57.68            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 57.45/57.68               (k2_tops_1 @ sk_A @ sk_B))))),
% 57.45/57.68      inference('sup-', [status(thm)], ['142', '143'])).
% 57.45/57.68  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf('146', plain,
% 57.45/57.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf('147', plain,
% 57.45/57.68      (![X41 : $i, X42 : $i, X43 : $i]:
% 57.45/57.68         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 57.45/57.68          | ((k7_subset_1 @ X42 @ X41 @ X43) = (k4_xboole_0 @ X41 @ X43)))),
% 57.45/57.68      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 57.45/57.68  thf('148', plain,
% 57.45/57.68      (![X0 : $i]:
% 57.45/57.68         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 57.45/57.68           = (k4_xboole_0 @ sk_B @ X0))),
% 57.45/57.68      inference('sup-', [status(thm)], ['146', '147'])).
% 57.45/57.68  thf('149', plain,
% 57.45/57.68      (((k1_tops_1 @ sk_A @ sk_B)
% 57.45/57.68         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 57.45/57.68      inference('demod', [status(thm)], ['144', '145', '148'])).
% 57.45/57.68  thf('150', plain,
% 57.45/57.68      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 57.45/57.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 57.45/57.68      inference('sup+', [status(thm)], ['141', '149'])).
% 57.45/57.68  thf('151', plain,
% 57.45/57.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf(fc9_tops_1, axiom,
% 57.45/57.68    (![A:$i,B:$i]:
% 57.45/57.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 57.45/57.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 57.45/57.68       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 57.45/57.68  thf('152', plain,
% 57.45/57.68      (![X55 : $i, X56 : $i]:
% 57.45/57.68         (~ (l1_pre_topc @ X55)
% 57.45/57.68          | ~ (v2_pre_topc @ X55)
% 57.45/57.68          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 57.45/57.68          | (v3_pre_topc @ (k1_tops_1 @ X55 @ X56) @ X55))),
% 57.45/57.68      inference('cnf', [status(esa)], [fc9_tops_1])).
% 57.45/57.68  thf('153', plain,
% 57.45/57.68      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 57.45/57.68        | ~ (v2_pre_topc @ sk_A)
% 57.45/57.68        | ~ (l1_pre_topc @ sk_A))),
% 57.45/57.68      inference('sup-', [status(thm)], ['151', '152'])).
% 57.45/57.68  thf('154', plain, ((v2_pre_topc @ sk_A)),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 57.45/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.45/57.68  thf('156', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 57.45/57.68      inference('demod', [status(thm)], ['153', '154', '155'])).
% 57.45/57.68  thf('157', plain,
% 57.45/57.68      (((v3_pre_topc @ sk_B @ sk_A))
% 57.45/57.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 57.45/57.68      inference('sup+', [status(thm)], ['150', '156'])).
% 57.45/57.68  thf('158', plain,
% 57.45/57.68      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 57.45/57.68      inference('split', [status(esa)], ['0'])).
% 57.45/57.68  thf('159', plain,
% 57.45/57.68      (~
% 57.45/57.68       (((k2_tops_1 @ sk_A @ sk_B)
% 57.45/57.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 57.45/57.68             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 57.45/57.68       ((v3_pre_topc @ sk_B @ sk_A))),
% 57.45/57.68      inference('sup-', [status(thm)], ['157', '158'])).
% 57.45/57.68  thf('160', plain, ($false),
% 57.45/57.68      inference('sat_resolution*', [status(thm)], ['1', '64', '65', '159'])).
% 57.45/57.68  
% 57.45/57.68  % SZS output end Refutation
% 57.45/57.68  
% 57.45/57.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
