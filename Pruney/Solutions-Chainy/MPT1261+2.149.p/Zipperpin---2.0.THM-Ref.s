%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UJorsvJahr

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:00 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 191 expanded)
%              Number of leaves         :   35 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          : 1150 (2291 expanded)
%              Number of equality atoms :   94 ( 154 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k4_subset_1 @ X18 @ X17 @ X19 )
        = ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
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

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('45',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('54',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('55',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('57',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('58',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','65'])).

thf('67',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','73'])).

thf('75',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','74'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('76',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('77',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('79',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_pre_topc @ X24 )
      | ( ( k2_pre_topc @ X24 @ X23 )
       != X23 )
      | ( v4_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('83',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UJorsvJahr
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:10:06 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.49/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.69  % Solved by: fo/fo7.sh
% 0.49/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.69  % done 855 iterations in 0.234s
% 0.49/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.69  % SZS output start Refutation
% 0.49/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.49/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.69  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.49/0.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.49/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.69  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.49/0.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.49/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.69  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.49/0.69  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.49/0.69  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.49/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(t77_tops_1, conjecture,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69           ( ( v4_pre_topc @ B @ A ) <=>
% 0.49/0.69             ( ( k2_tops_1 @ A @ B ) =
% 0.49/0.69               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.49/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.69    (~( ![A:$i]:
% 0.49/0.69        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.69          ( ![B:$i]:
% 0.49/0.69            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69              ( ( v4_pre_topc @ B @ A ) <=>
% 0.49/0.69                ( ( k2_tops_1 @ A @ B ) =
% 0.49/0.69                  ( k7_subset_1 @
% 0.49/0.69                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.49/0.69    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.49/0.69  thf('0', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69              (k1_tops_1 @ sk_A @ sk_B)))
% 0.49/0.69        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('1', plain,
% 0.49/0.69      (~
% 0.49/0.69       (((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.49/0.69       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('split', [status(esa)], ['0'])).
% 0.49/0.69  thf('2', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69             (k1_tops_1 @ sk_A @ sk_B)))
% 0.49/0.69        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('3', plain,
% 0.49/0.69      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.69      inference('split', [status(esa)], ['2'])).
% 0.49/0.69  thf('4', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(t52_pre_topc, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( l1_pre_topc @ A ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.49/0.69             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.49/0.69               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.49/0.69  thf('5', plain,
% 0.49/0.69      (![X23 : $i, X24 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.49/0.69          | ~ (v4_pre_topc @ X23 @ X24)
% 0.49/0.69          | ((k2_pre_topc @ X24 @ X23) = (X23))
% 0.49/0.69          | ~ (l1_pre_topc @ X24))),
% 0.49/0.69      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.49/0.69  thf('6', plain,
% 0.49/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.49/0.69        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.69  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('8', plain,
% 0.49/0.69      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('demod', [status(thm)], ['6', '7'])).
% 0.49/0.69  thf('9', plain,
% 0.49/0.69      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.49/0.69         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['3', '8'])).
% 0.49/0.69  thf('10', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(l78_tops_1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( l1_pre_topc @ A ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69           ( ( k2_tops_1 @ A @ B ) =
% 0.49/0.69             ( k7_subset_1 @
% 0.49/0.69               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.49/0.69               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.49/0.69  thf('11', plain,
% 0.49/0.69      (![X27 : $i, X28 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.49/0.69          | ((k2_tops_1 @ X28 @ X27)
% 0.49/0.69              = (k7_subset_1 @ (u1_struct_0 @ X28) @ 
% 0.49/0.69                 (k2_pre_topc @ X28 @ X27) @ (k1_tops_1 @ X28 @ X27)))
% 0.49/0.69          | ~ (l1_pre_topc @ X28))),
% 0.49/0.69      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.49/0.69  thf('12', plain,
% 0.49/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.69               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.49/0.69  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('14', plain,
% 0.49/0.69      (((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.49/0.69            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.49/0.69      inference('demod', [status(thm)], ['12', '13'])).
% 0.49/0.69  thf('15', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69             (k1_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['9', '14'])).
% 0.49/0.69  thf('16', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(redefinition_k7_subset_1, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i]:
% 0.49/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.69       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.49/0.69  thf('17', plain,
% 0.49/0.69      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.49/0.69          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 0.49/0.69      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.49/0.69  thf('18', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.49/0.69           = (k4_xboole_0 @ sk_B @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.69  thf('19', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['15', '18'])).
% 0.49/0.69  thf('20', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.49/0.69           = (k4_xboole_0 @ sk_B @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.69  thf('21', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69              (k1_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= (~
% 0.49/0.69             (((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('split', [status(esa)], ['0'])).
% 0.49/0.69  thf('22', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= (~
% 0.49/0.69             (((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['20', '21'])).
% 0.49/0.69  thf('23', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.49/0.69         <= (~
% 0.49/0.69             (((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.49/0.69             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['19', '22'])).
% 0.49/0.69  thf('24', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.49/0.69       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('simplify', [status(thm)], ['23'])).
% 0.49/0.69  thf('25', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.49/0.69       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.69      inference('split', [status(esa)], ['2'])).
% 0.49/0.69  thf('26', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(dt_k2_tops_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( ( l1_pre_topc @ A ) & 
% 0.49/0.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.49/0.69       ( m1_subset_1 @
% 0.49/0.69         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.49/0.69  thf('27', plain,
% 0.49/0.69      (![X25 : $i, X26 : $i]:
% 0.49/0.69         (~ (l1_pre_topc @ X25)
% 0.49/0.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.49/0.69          | (m1_subset_1 @ (k2_tops_1 @ X25 @ X26) @ 
% 0.49/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 0.49/0.69      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.49/0.69  thf('28', plain,
% 0.49/0.69      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.49/0.69         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.69        | ~ (l1_pre_topc @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['26', '27'])).
% 0.49/0.69  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('30', plain,
% 0.49/0.69      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.49/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('demod', [status(thm)], ['28', '29'])).
% 0.49/0.69  thf('31', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(redefinition_k4_subset_1, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i]:
% 0.49/0.69     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.49/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.69       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.49/0.69  thf('32', plain,
% 0.49/0.69      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.49/0.69          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 0.49/0.69          | ((k4_subset_1 @ X18 @ X17 @ X19) = (k2_xboole_0 @ X17 @ X19)))),
% 0.49/0.69      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.49/0.69  thf('33', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.49/0.69            = (k2_xboole_0 @ sk_B @ X0))
% 0.49/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['31', '32'])).
% 0.49/0.69  thf('34', plain,
% 0.49/0.69      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.49/0.69         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['30', '33'])).
% 0.49/0.69  thf('35', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(t65_tops_1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( l1_pre_topc @ A ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.69           ( ( k2_pre_topc @ A @ B ) =
% 0.49/0.69             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.49/0.69  thf('36', plain,
% 0.49/0.69      (![X29 : $i, X30 : $i]:
% 0.49/0.69         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.49/0.69          | ((k2_pre_topc @ X30 @ X29)
% 0.49/0.69              = (k4_subset_1 @ (u1_struct_0 @ X30) @ X29 @ 
% 0.49/0.69                 (k2_tops_1 @ X30 @ X29)))
% 0.49/0.69          | ~ (l1_pre_topc @ X30))),
% 0.49/0.69      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.49/0.69  thf('37', plain,
% 0.49/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.69        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.49/0.69            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.49/0.69  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('39', plain,
% 0.49/0.69      (((k2_pre_topc @ sk_A @ sk_B)
% 0.49/0.69         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.49/0.69      inference('demod', [status(thm)], ['37', '38'])).
% 0.49/0.69  thf('40', plain,
% 0.49/0.69      (((k2_pre_topc @ sk_A @ sk_B)
% 0.49/0.69         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['34', '39'])).
% 0.49/0.69  thf('41', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.49/0.69           = (k4_xboole_0 @ sk_B @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.69  thf('42', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69             (k1_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('split', [status(esa)], ['2'])).
% 0.49/0.69  thf('43', plain,
% 0.49/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup+', [status(thm)], ['41', '42'])).
% 0.49/0.69  thf(t36_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.49/0.69  thf('44', plain,
% 0.49/0.69      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.49/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.49/0.69  thf('45', plain,
% 0.49/0.69      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup+', [status(thm)], ['43', '44'])).
% 0.49/0.69  thf(t28_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.49/0.69  thf('46', plain,
% 0.49/0.69      (![X5 : $i, X6 : $i]:
% 0.49/0.69         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.49/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.49/0.69  thf('47', plain,
% 0.49/0.69      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.49/0.69          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['45', '46'])).
% 0.49/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.49/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.49/0.69  thf('48', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.69  thf('49', plain,
% 0.49/0.69      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.49/0.69          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('demod', [status(thm)], ['47', '48'])).
% 0.49/0.69  thf('50', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.69  thf(t100_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.49/0.69  thf('51', plain,
% 0.49/0.69      (![X2 : $i, X3 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X2 @ X3)
% 0.49/0.69           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.49/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.49/0.69  thf('52', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.49/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.49/0.69      inference('sup+', [status(thm)], ['50', '51'])).
% 0.49/0.69  thf('53', plain,
% 0.49/0.69      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.49/0.69          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.49/0.69             (k2_tops_1 @ sk_A @ sk_B))))
% 0.49/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.69      inference('sup+', [status(thm)], ['49', '52'])).
% 0.49/0.69  thf(t3_boole, axiom,
% 0.49/0.69    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.69  thf('54', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.69  thf(t48_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.69  thf('55', plain,
% 0.49/0.69      (![X15 : $i, X16 : $i]:
% 0.49/0.69         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.49/0.69           = (k3_xboole_0 @ X15 @ X16))),
% 0.49/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.69  thf('56', plain,
% 0.49/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.69      inference('sup+', [status(thm)], ['54', '55'])).
% 0.49/0.69  thf(t1_boole, axiom,
% 0.49/0.69    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.69  thf('57', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.49/0.69      inference('cnf', [status(esa)], [t1_boole])).
% 0.49/0.69  thf('58', plain,
% 0.49/0.69      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.49/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.49/0.69  thf(t44_xboole_1, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i]:
% 0.49/0.69     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.49/0.69       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.49/0.69  thf('59', plain,
% 0.49/0.69      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.49/0.69         ((r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14))
% 0.49/0.69          | ~ (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X14))),
% 0.49/0.69      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.49/0.69  thf('60', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['58', '59'])).
% 0.49/0.69  thf('61', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.49/0.69      inference('sup+', [status(thm)], ['57', '60'])).
% 0.49/0.69  thf('62', plain,
% 0.49/0.69      (![X5 : $i, X6 : $i]:
% 0.49/0.69         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.49/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.49/0.69  thf('63', plain,
% 0.49/0.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['61', '62'])).
% 0.49/0.69  thf('64', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.49/0.69  thf('65', plain,
% 0.49/0.69      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.69      inference('sup+', [status(thm)], ['63', '64'])).
% 0.49/0.69  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.69      inference('demod', [status(thm)], ['56', '65'])).
% 0.49/0.69  thf('67', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.69  thf('68', plain,
% 0.49/0.69      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.49/0.70      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.49/0.70  thf('69', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.49/0.70      inference('sup+', [status(thm)], ['67', '68'])).
% 0.49/0.70  thf('70', plain,
% 0.49/0.70      (![X5 : $i, X6 : $i]:
% 0.49/0.70         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.49/0.70      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.49/0.70  thf('71', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['69', '70'])).
% 0.49/0.70  thf('72', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((k4_xboole_0 @ X0 @ X1)
% 0.49/0.70           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.49/0.70      inference('sup+', [status(thm)], ['50', '51'])).
% 0.49/0.70  thf('73', plain,
% 0.49/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.49/0.70      inference('sup+', [status(thm)], ['71', '72'])).
% 0.49/0.70  thf('74', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.70      inference('demod', [status(thm)], ['66', '73'])).
% 0.49/0.70  thf('75', plain,
% 0.49/0.70      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.49/0.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.70      inference('demod', [status(thm)], ['53', '74'])).
% 0.49/0.70  thf(t39_xboole_1, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.49/0.70  thf('76', plain,
% 0.49/0.70      (![X9 : $i, X10 : $i]:
% 0.49/0.70         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.49/0.70           = (k2_xboole_0 @ X9 @ X10))),
% 0.49/0.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.49/0.70  thf('77', plain,
% 0.49/0.70      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.49/0.70          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.49/0.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.70      inference('sup+', [status(thm)], ['75', '76'])).
% 0.49/0.70  thf('78', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.49/0.70      inference('cnf', [status(esa)], [t1_boole])).
% 0.49/0.70  thf('79', plain,
% 0.49/0.70      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.49/0.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.70      inference('demod', [status(thm)], ['77', '78'])).
% 0.49/0.70  thf('80', plain,
% 0.49/0.70      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.49/0.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.70      inference('sup+', [status(thm)], ['40', '79'])).
% 0.49/0.70  thf('81', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('82', plain,
% 0.49/0.70      (![X23 : $i, X24 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.49/0.70          | ~ (v2_pre_topc @ X24)
% 0.49/0.70          | ((k2_pre_topc @ X24 @ X23) != (X23))
% 0.49/0.70          | (v4_pre_topc @ X23 @ X24)
% 0.49/0.70          | ~ (l1_pre_topc @ X24))),
% 0.49/0.70      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.49/0.70  thf('83', plain,
% 0.49/0.70      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.70        | (v4_pre_topc @ sk_B @ sk_A)
% 0.49/0.70        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.49/0.70        | ~ (v2_pre_topc @ sk_A))),
% 0.49/0.70      inference('sup-', [status(thm)], ['81', '82'])).
% 0.49/0.70  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('86', plain,
% 0.49/0.70      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.49/0.70  thf('87', plain,
% 0.49/0.70      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.49/0.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['80', '86'])).
% 0.49/0.70  thf('88', plain,
% 0.49/0.70      (((v4_pre_topc @ sk_B @ sk_A))
% 0.49/0.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.49/0.70      inference('simplify', [status(thm)], ['87'])).
% 0.49/0.70  thf('89', plain,
% 0.49/0.70      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.70      inference('split', [status(esa)], ['0'])).
% 0.49/0.70  thf('90', plain,
% 0.49/0.70      (~
% 0.49/0.70       (((k2_tops_1 @ sk_A @ sk_B)
% 0.49/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.49/0.70             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.49/0.70       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.70      inference('sup-', [status(thm)], ['88', '89'])).
% 0.49/0.70  thf('91', plain, ($false),
% 0.49/0.70      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '90'])).
% 0.49/0.70  
% 0.49/0.70  % SZS output end Refutation
% 0.49/0.70  
% 0.49/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
