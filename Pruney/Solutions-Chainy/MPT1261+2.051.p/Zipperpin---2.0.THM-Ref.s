%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.amMCNWKKPR

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:45 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 339 expanded)
%              Number of leaves         :   43 ( 113 expanded)
%              Depth                    :   20
%              Number of atoms          : 1529 (4319 expanded)
%              Number of equality atoms :  122 ( 257 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v4_pre_topc @ X35 @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k2_tops_1 @ X42 @ X41 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k2_pre_topc @ X42 @ X41 ) @ ( k1_tops_1 @ X42 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k7_subset_1 @ X25 @ X24 @ X26 )
        = ( k4_xboole_0 @ X24 @ X26 ) ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k4_subset_1 @ X22 @ X21 @ X23 )
        = ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
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
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k2_pre_topc @ X46 @ X45 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X46 ) @ X45 @ ( k2_tops_1 @ X46 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X32: $i,X34: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( r1_tarski @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('49',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('51',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X44 @ X43 ) @ X43 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X32: $i,X34: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( r1_tarski @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('58',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('62',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('63',plain,
    ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','64'])).

thf('66',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('68',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('75',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('76',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('77',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('79',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_tarski @ X12 @ X11 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('80',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X30 @ X31 ) )
      = ( k3_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X30 @ X31 ) )
      = ( k3_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('84',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['78','85'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('87',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('88',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('91',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('93',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','92','93'])).

thf('95',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','94'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('96',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('97',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('99',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','102'])).

thf('104',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('106',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X39 @ X40 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('107',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['104','110'])).

thf('112',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.amMCNWKKPR
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.58/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.78  % Solved by: fo/fo7.sh
% 0.58/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.78  % done 1083 iterations in 0.351s
% 0.58/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.78  % SZS output start Refutation
% 0.58/0.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.78  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.58/0.78  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.58/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.78  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.58/0.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.78  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.58/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.78  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.58/0.78  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.58/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.78  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.58/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.78  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.58/0.78  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.58/0.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.58/0.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.78  thf(t77_tops_1, conjecture,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.78       ( ![B:$i]:
% 0.58/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.78           ( ( v4_pre_topc @ B @ A ) <=>
% 0.58/0.78             ( ( k2_tops_1 @ A @ B ) =
% 0.58/0.78               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.58/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.78    (~( ![A:$i]:
% 0.58/0.78        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.78          ( ![B:$i]:
% 0.58/0.78            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.78              ( ( v4_pre_topc @ B @ A ) <=>
% 0.58/0.78                ( ( k2_tops_1 @ A @ B ) =
% 0.58/0.78                  ( k7_subset_1 @
% 0.58/0.78                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.58/0.78    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.58/0.78  thf('0', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78              (k1_tops_1 @ sk_A @ sk_B)))
% 0.58/0.78        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('1', plain,
% 0.58/0.78      (~
% 0.58/0.78       (((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.58/0.78       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.78      inference('split', [status(esa)], ['0'])).
% 0.58/0.78  thf('2', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78             (k1_tops_1 @ sk_A @ sk_B)))
% 0.58/0.78        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('3', plain,
% 0.58/0.78      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.58/0.78      inference('split', [status(esa)], ['2'])).
% 0.58/0.78  thf('4', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(t52_pre_topc, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( l1_pre_topc @ A ) =>
% 0.58/0.78       ( ![B:$i]:
% 0.58/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.78           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.58/0.78             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.58/0.78               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.58/0.78  thf('5', plain,
% 0.58/0.78      (![X35 : $i, X36 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.58/0.78          | ~ (v4_pre_topc @ X35 @ X36)
% 0.58/0.78          | ((k2_pre_topc @ X36 @ X35) = (X35))
% 0.58/0.78          | ~ (l1_pre_topc @ X36))),
% 0.58/0.78      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.58/0.78  thf('6', plain,
% 0.58/0.78      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.78        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.58/0.78        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['4', '5'])).
% 0.58/0.78  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('8', plain,
% 0.58/0.78      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['6', '7'])).
% 0.58/0.78  thf('9', plain,
% 0.58/0.78      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.58/0.78         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['3', '8'])).
% 0.58/0.78  thf('10', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(l78_tops_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( l1_pre_topc @ A ) =>
% 0.58/0.78       ( ![B:$i]:
% 0.58/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.78           ( ( k2_tops_1 @ A @ B ) =
% 0.58/0.78             ( k7_subset_1 @
% 0.58/0.78               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.58/0.78               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.58/0.78  thf('11', plain,
% 0.58/0.78      (![X41 : $i, X42 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.58/0.78          | ((k2_tops_1 @ X42 @ X41)
% 0.58/0.78              = (k7_subset_1 @ (u1_struct_0 @ X42) @ 
% 0.58/0.78                 (k2_pre_topc @ X42 @ X41) @ (k1_tops_1 @ X42 @ X41)))
% 0.58/0.78          | ~ (l1_pre_topc @ X42))),
% 0.58/0.78      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.58/0.78  thf('12', plain,
% 0.58/0.78      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.78        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.78               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.78  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('14', plain,
% 0.58/0.78      (((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.58/0.78            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.78      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.78  thf('15', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78             (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.58/0.78      inference('sup+', [status(thm)], ['9', '14'])).
% 0.58/0.78  thf('16', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(redefinition_k7_subset_1, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.78       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.58/0.78  thf('17', plain,
% 0.58/0.78      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.58/0.78          | ((k7_subset_1 @ X25 @ X24 @ X26) = (k4_xboole_0 @ X24 @ X26)))),
% 0.58/0.78      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.58/0.78  thf('18', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.58/0.78           = (k4_xboole_0 @ sk_B @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.78  thf('19', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['15', '18'])).
% 0.58/0.78  thf('20', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.58/0.78           = (k4_xboole_0 @ sk_B @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.78  thf('21', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78              (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= (~
% 0.58/0.78             (((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('split', [status(esa)], ['0'])).
% 0.58/0.78  thf('22', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= (~
% 0.58/0.78             (((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.78  thf('23', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.58/0.78         <= (~
% 0.58/0.78             (((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.58/0.78             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['19', '22'])).
% 0.58/0.78  thf('24', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.58/0.78       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.78      inference('simplify', [status(thm)], ['23'])).
% 0.58/0.78  thf('25', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.58/0.78       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.78      inference('split', [status(esa)], ['2'])).
% 0.58/0.78  thf('26', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(dt_k2_tops_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ( l1_pre_topc @ A ) & 
% 0.58/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.78       ( m1_subset_1 @
% 0.58/0.78         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.58/0.78  thf('27', plain,
% 0.58/0.78      (![X37 : $i, X38 : $i]:
% 0.58/0.78         (~ (l1_pre_topc @ X37)
% 0.58/0.78          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.58/0.78          | (m1_subset_1 @ (k2_tops_1 @ X37 @ X38) @ 
% 0.58/0.78             (k1_zfmisc_1 @ (u1_struct_0 @ X37))))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.58/0.78  thf('28', plain,
% 0.58/0.78      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.58/0.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.78        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.78  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('30', plain,
% 0.58/0.78      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['28', '29'])).
% 0.58/0.78  thf('31', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(redefinition_k4_subset_1, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.58/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.58/0.78       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.58/0.78  thf('32', plain,
% 0.58/0.78      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.58/0.78          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22))
% 0.58/0.78          | ((k4_subset_1 @ X22 @ X21 @ X23) = (k2_xboole_0 @ X21 @ X23)))),
% 0.58/0.78      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.58/0.78  thf('33', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.58/0.78            = (k2_xboole_0 @ sk_B @ X0))
% 0.58/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['31', '32'])).
% 0.58/0.78  thf('34', plain,
% 0.58/0.78      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.58/0.78         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['30', '33'])).
% 0.58/0.78  thf('35', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(t65_tops_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( l1_pre_topc @ A ) =>
% 0.58/0.78       ( ![B:$i]:
% 0.58/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.78           ( ( k2_pre_topc @ A @ B ) =
% 0.58/0.78             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.58/0.78  thf('36', plain,
% 0.58/0.78      (![X45 : $i, X46 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.58/0.78          | ((k2_pre_topc @ X46 @ X45)
% 0.58/0.78              = (k4_subset_1 @ (u1_struct_0 @ X46) @ X45 @ 
% 0.58/0.78                 (k2_tops_1 @ X46 @ X45)))
% 0.58/0.78          | ~ (l1_pre_topc @ X46))),
% 0.58/0.78      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.58/0.78  thf('37', plain,
% 0.58/0.78      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.78        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.58/0.78            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['35', '36'])).
% 0.58/0.78  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('39', plain,
% 0.58/0.78      (((k2_pre_topc @ sk_A @ sk_B)
% 0.58/0.78         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.78      inference('demod', [status(thm)], ['37', '38'])).
% 0.58/0.78  thf('40', plain,
% 0.58/0.78      (((k2_pre_topc @ sk_A @ sk_B)
% 0.58/0.78         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.78      inference('sup+', [status(thm)], ['34', '39'])).
% 0.58/0.78  thf('41', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.58/0.78           = (k4_xboole_0 @ sk_B @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.78  thf('42', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78             (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('split', [status(esa)], ['2'])).
% 0.58/0.78  thf('43', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['41', '42'])).
% 0.58/0.78  thf(t36_xboole_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.58/0.78  thf('44', plain,
% 0.58/0.78      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.58/0.78      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.58/0.78  thf(t3_subset, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.78  thf('45', plain,
% 0.58/0.78      (![X32 : $i, X34 : $i]:
% 0.58/0.78         ((m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X34)) | ~ (r1_tarski @ X32 @ X34))),
% 0.58/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.78  thf('46', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['44', '45'])).
% 0.58/0.78  thf('47', plain,
% 0.58/0.78      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['43', '46'])).
% 0.58/0.78  thf(d5_subset_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.78       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.58/0.78  thf('48', plain,
% 0.58/0.78      (![X15 : $i, X16 : $i]:
% 0.58/0.78         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 0.58/0.78          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.58/0.78      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.58/0.78  thf('49', plain,
% 0.58/0.78      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.58/0.78          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['47', '48'])).
% 0.58/0.78  thf('50', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(t44_tops_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( l1_pre_topc @ A ) =>
% 0.58/0.78       ( ![B:$i]:
% 0.58/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.78           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.58/0.78  thf('51', plain,
% 0.58/0.78      (![X43 : $i, X44 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.58/0.78          | (r1_tarski @ (k1_tops_1 @ X44 @ X43) @ X43)
% 0.58/0.78          | ~ (l1_pre_topc @ X44))),
% 0.58/0.78      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.58/0.78  thf('52', plain,
% 0.58/0.78      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.58/0.78      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.78  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('54', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.58/0.78      inference('demod', [status(thm)], ['52', '53'])).
% 0.58/0.78  thf('55', plain,
% 0.58/0.78      (![X32 : $i, X34 : $i]:
% 0.58/0.78         ((m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X34)) | ~ (r1_tarski @ X32 @ X34))),
% 0.58/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.78  thf('56', plain,
% 0.58/0.78      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.58/0.78      inference('sup-', [status(thm)], ['54', '55'])).
% 0.58/0.78  thf('57', plain,
% 0.58/0.78      (![X15 : $i, X16 : $i]:
% 0.58/0.78         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 0.58/0.78          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.58/0.78      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.58/0.78  thf('58', plain,
% 0.58/0.78      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.58/0.78         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['56', '57'])).
% 0.58/0.78  thf('59', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['41', '42'])).
% 0.58/0.78  thf('60', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['58', '59'])).
% 0.58/0.78  thf('61', plain,
% 0.58/0.78      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.58/0.78      inference('sup-', [status(thm)], ['54', '55'])).
% 0.58/0.78  thf(involutiveness_k3_subset_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.78       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.58/0.78  thf('62', plain,
% 0.58/0.78      (![X19 : $i, X20 : $i]:
% 0.58/0.78         (((k3_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X19)) = (X19))
% 0.58/0.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.58/0.78      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.58/0.78  thf('63', plain,
% 0.58/0.78      (((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.58/0.78         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.58/0.78      inference('sup-', [status(thm)], ['61', '62'])).
% 0.58/0.78  thf('64', plain,
% 0.58/0.78      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.58/0.78          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['60', '63'])).
% 0.58/0.78  thf('65', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('demod', [status(thm)], ['49', '64'])).
% 0.58/0.78  thf('66', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['41', '42'])).
% 0.58/0.78  thf(t48_xboole_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.78  thf('67', plain,
% 0.58/0.78      (![X7 : $i, X8 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.58/0.78           = (k3_xboole_0 @ X7 @ X8))),
% 0.58/0.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.78  thf('68', plain,
% 0.58/0.78      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.58/0.78          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['66', '67'])).
% 0.58/0.78  thf('69', plain,
% 0.58/0.78      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['65', '68'])).
% 0.58/0.78  thf('70', plain,
% 0.58/0.78      (![X7 : $i, X8 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.58/0.78           = (k3_xboole_0 @ X7 @ X8))),
% 0.58/0.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.78  thf('71', plain,
% 0.58/0.78      (![X7 : $i, X8 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.58/0.78           = (k3_xboole_0 @ X7 @ X8))),
% 0.58/0.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.78  thf('72', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.78           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.58/0.78      inference('sup+', [status(thm)], ['70', '71'])).
% 0.58/0.78  thf('73', plain,
% 0.58/0.78      ((((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.58/0.78          = (k3_xboole_0 @ sk_B @ 
% 0.58/0.78             (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['69', '72'])).
% 0.58/0.78  thf('74', plain,
% 0.58/0.78      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.58/0.78         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['56', '57'])).
% 0.58/0.78  thf('75', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['58', '59'])).
% 0.58/0.78  thf('76', plain,
% 0.58/0.78      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.58/0.78         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['56', '57'])).
% 0.58/0.78  thf('77', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['58', '59'])).
% 0.58/0.78  thf('78', plain,
% 0.58/0.78      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 0.58/0.78  thf(commutativity_k2_tarski, axiom,
% 0.58/0.78    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.58/0.78  thf('79', plain,
% 0.58/0.78      (![X11 : $i, X12 : $i]:
% 0.58/0.78         ((k2_tarski @ X12 @ X11) = (k2_tarski @ X11 @ X12))),
% 0.58/0.78      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.58/0.78  thf(t12_setfam_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.78  thf('80', plain,
% 0.58/0.78      (![X30 : $i, X31 : $i]:
% 0.58/0.78         ((k1_setfam_1 @ (k2_tarski @ X30 @ X31)) = (k3_xboole_0 @ X30 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.58/0.78  thf('81', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.78      inference('sup+', [status(thm)], ['79', '80'])).
% 0.58/0.78  thf('82', plain,
% 0.58/0.78      (![X30 : $i, X31 : $i]:
% 0.58/0.78         ((k1_setfam_1 @ (k2_tarski @ X30 @ X31)) = (k3_xboole_0 @ X30 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.58/0.78  thf('83', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.78      inference('sup+', [status(thm)], ['81', '82'])).
% 0.58/0.78  thf(t100_xboole_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.78  thf('84', plain,
% 0.58/0.78      (![X1 : $i, X2 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X1 @ X2)
% 0.58/0.78           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.58/0.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.78  thf('85', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X0 @ X1)
% 0.58/0.78           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.78      inference('sup+', [status(thm)], ['83', '84'])).
% 0.58/0.78  thf('86', plain,
% 0.58/0.78      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.58/0.78          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.58/0.78             (k2_tops_1 @ sk_A @ sk_B))))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['78', '85'])).
% 0.58/0.78  thf(t3_boole, axiom,
% 0.58/0.78    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.78  thf('87', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.58/0.78      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.78  thf('88', plain,
% 0.58/0.78      (![X7 : $i, X8 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.58/0.78           = (k3_xboole_0 @ X7 @ X8))),
% 0.58/0.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.78  thf('89', plain,
% 0.58/0.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['87', '88'])).
% 0.58/0.78  thf(idempotence_k3_xboole_0, axiom,
% 0.58/0.78    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.58/0.78  thf('90', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.58/0.78      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.58/0.78  thf('91', plain,
% 0.58/0.78      (![X1 : $i, X2 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X1 @ X2)
% 0.58/0.78           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.58/0.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.78  thf('92', plain,
% 0.58/0.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['90', '91'])).
% 0.58/0.78  thf(t2_boole, axiom,
% 0.58/0.78    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.58/0.78  thf('93', plain,
% 0.58/0.78      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.78      inference('cnf', [status(esa)], [t2_boole])).
% 0.58/0.78  thf('94', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.78      inference('demod', [status(thm)], ['89', '92', '93'])).
% 0.58/0.78  thf('95', plain,
% 0.58/0.78      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('demod', [status(thm)], ['86', '94'])).
% 0.58/0.78  thf(t98_xboole_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.58/0.78  thf('96', plain,
% 0.58/0.78      (![X9 : $i, X10 : $i]:
% 0.58/0.78         ((k2_xboole_0 @ X9 @ X10)
% 0.58/0.78           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.58/0.78      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.58/0.78  thf('97', plain,
% 0.58/0.78      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.58/0.78          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['95', '96'])).
% 0.58/0.78  thf('98', plain,
% 0.58/0.78      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.78      inference('cnf', [status(esa)], [t2_boole])).
% 0.58/0.78  thf('99', plain,
% 0.58/0.78      (![X1 : $i, X2 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X1 @ X2)
% 0.58/0.78           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.58/0.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.78  thf('100', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['98', '99'])).
% 0.58/0.78  thf('101', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.58/0.78      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.78  thf('102', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['100', '101'])).
% 0.58/0.78  thf('103', plain,
% 0.58/0.78      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('demod', [status(thm)], ['97', '102'])).
% 0.58/0.78  thf('104', plain,
% 0.58/0.78      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.58/0.78         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.78                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.78                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.78      inference('sup+', [status(thm)], ['40', '103'])).
% 0.58/0.78  thf('105', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(fc1_tops_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.58/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.78       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.58/0.78  thf('106', plain,
% 0.58/0.78      (![X39 : $i, X40 : $i]:
% 0.58/0.78         (~ (l1_pre_topc @ X39)
% 0.58/0.78          | ~ (v2_pre_topc @ X39)
% 0.58/0.78          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.58/0.78          | (v4_pre_topc @ (k2_pre_topc @ X39 @ X40) @ X39))),
% 0.58/0.78      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.58/0.78  thf('107', plain,
% 0.58/0.78      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.58/0.78        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.78        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['105', '106'])).
% 0.58/0.79  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('110', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.58/0.79      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.58/0.79  thf('111', plain,
% 0.58/0.79      (((v4_pre_topc @ sk_B @ sk_A))
% 0.58/0.79         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.79                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.79                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.58/0.79      inference('sup+', [status(thm)], ['104', '110'])).
% 0.58/0.79  thf('112', plain,
% 0.58/0.79      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.58/0.79      inference('split', [status(esa)], ['0'])).
% 0.58/0.79  thf('113', plain,
% 0.58/0.79      (~
% 0.58/0.79       (((k2_tops_1 @ sk_A @ sk_B)
% 0.58/0.79          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.58/0.79             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.58/0.79       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.58/0.79      inference('sup-', [status(thm)], ['111', '112'])).
% 0.58/0.79  thf('114', plain, ($false),
% 0.58/0.79      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '113'])).
% 0.58/0.79  
% 0.58/0.79  % SZS output end Refutation
% 0.58/0.79  
% 0.58/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
