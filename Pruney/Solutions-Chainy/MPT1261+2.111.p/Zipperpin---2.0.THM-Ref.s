%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ei9wXefxW4

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:54 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 800 expanded)
%              Number of leaves         :   36 ( 244 expanded)
%              Depth                    :   16
%              Number of atoms          : 1645 (11408 expanded)
%              Number of equality atoms :  120 ( 677 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k2_pre_topc @ X35 @ X34 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X35 ) @ X34 @ ( k2_tops_1 @ X35 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('42',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k1_tops_1 @ X37 @ X36 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 @ ( k2_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('46',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('56',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
          = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('69',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('71',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('73',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('75',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('77',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('80',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('82',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','71','78','79','80','81'])).

thf('83',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('84',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = ( k2_subset_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('85',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('86',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X22 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('89',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['82','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('92',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('93',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k2_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['91','94'])).

thf('96',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('99',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['82','89'])).

thf('101',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('104',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X30 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('105',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['102','108'])).

thf('110',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('111',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ei9wXefxW4
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:40:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.69/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.90  % Solved by: fo/fo7.sh
% 0.69/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.90  % done 442 iterations in 0.432s
% 0.69/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.90  % SZS output start Refutation
% 0.69/0.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.90  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.69/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.90  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.69/0.90  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.69/0.90  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.90  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.69/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.90  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.69/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.90  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.69/0.90  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.69/0.90  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.69/0.90  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.69/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.90  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.69/0.90  thf(t77_tops_1, conjecture,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.90       ( ![B:$i]:
% 0.69/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.90           ( ( v4_pre_topc @ B @ A ) <=>
% 0.69/0.90             ( ( k2_tops_1 @ A @ B ) =
% 0.69/0.90               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.69/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.90    (~( ![A:$i]:
% 0.69/0.90        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.69/0.90          ( ![B:$i]:
% 0.69/0.90            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.90              ( ( v4_pre_topc @ B @ A ) <=>
% 0.69/0.90                ( ( k2_tops_1 @ A @ B ) =
% 0.69/0.90                  ( k7_subset_1 @
% 0.69/0.90                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.69/0.90    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.69/0.90  thf('0', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90              (k1_tops_1 @ sk_A @ sk_B)))
% 0.69/0.90        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('1', plain,
% 0.69/0.90      (~
% 0.69/0.90       (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.69/0.90       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.69/0.90      inference('split', [status(esa)], ['0'])).
% 0.69/0.90  thf('2', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90             (k1_tops_1 @ sk_A @ sk_B)))
% 0.69/0.90        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('3', plain,
% 0.69/0.90      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.90      inference('split', [status(esa)], ['2'])).
% 0.69/0.90  thf('4', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(t52_pre_topc, axiom,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( l1_pre_topc @ A ) =>
% 0.69/0.90       ( ![B:$i]:
% 0.69/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.90           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.69/0.90             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.69/0.90               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.69/0.90  thf('5', plain,
% 0.69/0.90      (![X26 : $i, X27 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.69/0.90          | ~ (v4_pre_topc @ X26 @ X27)
% 0.69/0.90          | ((k2_pre_topc @ X27 @ X26) = (X26))
% 0.69/0.90          | ~ (l1_pre_topc @ X27))),
% 0.69/0.90      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.69/0.90  thf('6', plain,
% 0.69/0.90      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.90        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.69/0.90        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.69/0.90      inference('sup-', [status(thm)], ['4', '5'])).
% 0.69/0.90  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('8', plain,
% 0.69/0.90      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.69/0.90      inference('demod', [status(thm)], ['6', '7'])).
% 0.69/0.90  thf('9', plain,
% 0.69/0.90      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.69/0.90         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['3', '8'])).
% 0.69/0.90  thf('10', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(l78_tops_1, axiom,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( l1_pre_topc @ A ) =>
% 0.69/0.90       ( ![B:$i]:
% 0.69/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.90           ( ( k2_tops_1 @ A @ B ) =
% 0.69/0.90             ( k7_subset_1 @
% 0.69/0.90               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.69/0.90               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.69/0.90  thf('11', plain,
% 0.69/0.90      (![X32 : $i, X33 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.69/0.90          | ((k2_tops_1 @ X33 @ X32)
% 0.69/0.90              = (k7_subset_1 @ (u1_struct_0 @ X33) @ 
% 0.69/0.90                 (k2_pre_topc @ X33 @ X32) @ (k1_tops_1 @ X33 @ X32)))
% 0.69/0.90          | ~ (l1_pre_topc @ X33))),
% 0.69/0.90      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.69/0.90  thf('12', plain,
% 0.69/0.90      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.90        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.90               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.90  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('14', plain,
% 0.69/0.90      (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.69/0.90            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.90      inference('demod', [status(thm)], ['12', '13'])).
% 0.69/0.90  thf('15', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90             (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.90      inference('sup+', [status(thm)], ['9', '14'])).
% 0.69/0.90  thf('16', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(redefinition_k7_subset_1, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.90       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.69/0.90  thf('17', plain,
% 0.69/0.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.69/0.90          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 0.69/0.90      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.69/0.90  thf('18', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.69/0.90           = (k4_xboole_0 @ sk_B @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['16', '17'])).
% 0.69/0.90  thf('19', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.90      inference('demod', [status(thm)], ['15', '18'])).
% 0.69/0.90  thf('20', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.69/0.90           = (k4_xboole_0 @ sk_B @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['16', '17'])).
% 0.69/0.90  thf('21', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90              (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= (~
% 0.69/0.90             (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('split', [status(esa)], ['0'])).
% 0.69/0.90  thf('22', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= (~
% 0.69/0.90             (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['20', '21'])).
% 0.69/0.90  thf('23', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.69/0.90         <= (~
% 0.69/0.90             (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.69/0.90             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['19', '22'])).
% 0.69/0.90  thf('24', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.69/0.90       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.69/0.90      inference('simplify', [status(thm)], ['23'])).
% 0.69/0.90  thf('25', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.69/0.90       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.69/0.90      inference('split', [status(esa)], ['2'])).
% 0.69/0.90  thf('26', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(dt_k2_tops_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( ( l1_pre_topc @ A ) & 
% 0.69/0.90         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.69/0.90       ( m1_subset_1 @
% 0.69/0.90         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.69/0.90  thf('27', plain,
% 0.69/0.90      (![X28 : $i, X29 : $i]:
% 0.69/0.90         (~ (l1_pre_topc @ X28)
% 0.69/0.90          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.69/0.90          | (m1_subset_1 @ (k2_tops_1 @ X28 @ X29) @ 
% 0.69/0.90             (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.69/0.90  thf('28', plain,
% 0.69/0.90      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.69/0.90         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.90        | ~ (l1_pre_topc @ sk_A))),
% 0.69/0.90      inference('sup-', [status(thm)], ['26', '27'])).
% 0.69/0.90  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('30', plain,
% 0.69/0.90      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.69/0.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('demod', [status(thm)], ['28', '29'])).
% 0.69/0.90  thf('31', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(redefinition_k4_subset_1, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.69/0.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.90       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.69/0.90  thf('32', plain,
% 0.69/0.90      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.69/0.90          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.69/0.90          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.69/0.90      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.69/0.90  thf('33', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.69/0.90            = (k2_xboole_0 @ sk_B @ X0))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['31', '32'])).
% 0.69/0.90  thf('34', plain,
% 0.69/0.90      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.90         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['30', '33'])).
% 0.69/0.90  thf('35', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(t65_tops_1, axiom,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( l1_pre_topc @ A ) =>
% 0.69/0.90       ( ![B:$i]:
% 0.69/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.90           ( ( k2_pre_topc @ A @ B ) =
% 0.69/0.90             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.69/0.90  thf('36', plain,
% 0.69/0.90      (![X34 : $i, X35 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.69/0.90          | ((k2_pre_topc @ X35 @ X34)
% 0.69/0.90              = (k4_subset_1 @ (u1_struct_0 @ X35) @ X34 @ 
% 0.69/0.90                 (k2_tops_1 @ X35 @ X34)))
% 0.69/0.90          | ~ (l1_pre_topc @ X35))),
% 0.69/0.90      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.69/0.90  thf('37', plain,
% 0.69/0.90      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.90        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.69/0.90            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['35', '36'])).
% 0.69/0.90  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('39', plain,
% 0.69/0.90      (((k2_pre_topc @ sk_A @ sk_B)
% 0.69/0.90         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.90      inference('demod', [status(thm)], ['37', '38'])).
% 0.69/0.90  thf('40', plain,
% 0.69/0.90      (((k2_pre_topc @ sk_A @ sk_B)
% 0.69/0.90         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.90      inference('sup+', [status(thm)], ['34', '39'])).
% 0.69/0.90  thf('41', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(t74_tops_1, axiom,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( l1_pre_topc @ A ) =>
% 0.69/0.90       ( ![B:$i]:
% 0.69/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.90           ( ( k1_tops_1 @ A @ B ) =
% 0.69/0.90             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.69/0.90  thf('42', plain,
% 0.69/0.90      (![X36 : $i, X37 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.69/0.90          | ((k1_tops_1 @ X37 @ X36)
% 0.69/0.90              = (k7_subset_1 @ (u1_struct_0 @ X37) @ X36 @ 
% 0.69/0.90                 (k2_tops_1 @ X37 @ X36)))
% 0.69/0.90          | ~ (l1_pre_topc @ X37))),
% 0.69/0.90      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.69/0.90  thf('43', plain,
% 0.69/0.90      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.90        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.69/0.90            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['41', '42'])).
% 0.69/0.90  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('45', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.69/0.90           = (k4_xboole_0 @ sk_B @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['16', '17'])).
% 0.69/0.90  thf('46', plain,
% 0.69/0.90      (((k1_tops_1 @ sk_A @ sk_B)
% 0.69/0.90         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.90      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.69/0.90  thf(t36_xboole_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.69/0.90  thf('47', plain,
% 0.69/0.90      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.69/0.90      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.69/0.90  thf(t3_subset, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.69/0.90  thf('48', plain,
% 0.69/0.90      (![X23 : $i, X25 : $i]:
% 0.69/0.90         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 0.69/0.90      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.90  thf('49', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['47', '48'])).
% 0.69/0.90  thf(dt_k3_subset_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.90       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.69/0.90  thf('50', plain,
% 0.69/0.90      (![X13 : $i, X14 : $i]:
% 0.69/0.90         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 0.69/0.90          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.69/0.90  thf('51', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (m1_subset_1 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 0.69/0.90          (k1_zfmisc_1 @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['49', '50'])).
% 0.69/0.90  thf('52', plain,
% 0.69/0.90      (![X13 : $i, X14 : $i]:
% 0.69/0.90         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 0.69/0.90          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.69/0.90  thf('53', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (m1_subset_1 @ 
% 0.69/0.90          (k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))) @ 
% 0.69/0.90          (k1_zfmisc_1 @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['51', '52'])).
% 0.69/0.90  thf('54', plain,
% 0.69/0.90      ((m1_subset_1 @ 
% 0.69/0.90        (k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.69/0.90        (k1_zfmisc_1 @ sk_B))),
% 0.69/0.90      inference('sup+', [status(thm)], ['46', '53'])).
% 0.69/0.90  thf('55', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.69/0.90           = (k4_xboole_0 @ sk_B @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['16', '17'])).
% 0.69/0.90  thf('56', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90             (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('split', [status(esa)], ['2'])).
% 0.69/0.90  thf('57', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['55', '56'])).
% 0.69/0.90  thf('58', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['47', '48'])).
% 0.69/0.90  thf('59', plain,
% 0.69/0.90      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['57', '58'])).
% 0.69/0.90  thf('60', plain,
% 0.69/0.90      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.69/0.90          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.69/0.90          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.69/0.90      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.69/0.90  thf('61', plain,
% 0.69/0.90      ((![X0 : $i]:
% 0.69/0.90          (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.69/0.90             = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 0.69/0.90           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['59', '60'])).
% 0.69/0.90  thf('62', plain,
% 0.69/0.90      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.69/0.90          (k3_subset_1 @ sk_B @ 
% 0.69/0.90           (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.69/0.90             (k3_subset_1 @ sk_B @ 
% 0.69/0.90              (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['54', '61'])).
% 0.69/0.90  thf('63', plain,
% 0.69/0.90      (((k1_tops_1 @ sk_A @ sk_B)
% 0.69/0.90         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.90      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.69/0.90  thf('64', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.69/0.90      inference('sup-', [status(thm)], ['47', '48'])).
% 0.69/0.90  thf(d5_subset_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.90       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.69/0.90  thf('65', plain,
% 0.69/0.90      (![X11 : $i, X12 : $i]:
% 0.69/0.90         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.69/0.90          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.69/0.90      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.69/0.90  thf('66', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.69/0.90           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['64', '65'])).
% 0.69/0.90  thf('67', plain,
% 0.69/0.90      (((k3_subset_1 @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.69/0.90         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.90      inference('sup+', [status(thm)], ['63', '66'])).
% 0.69/0.90  thf('68', plain,
% 0.69/0.90      (((k1_tops_1 @ sk_A @ sk_B)
% 0.69/0.90         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.90      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.69/0.90  thf('69', plain,
% 0.69/0.90      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.69/0.90         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.90      inference('demod', [status(thm)], ['67', '68'])).
% 0.69/0.90  thf('70', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['55', '56'])).
% 0.69/0.90  thf('71', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          = (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['69', '70'])).
% 0.69/0.90  thf('72', plain,
% 0.69/0.90      (((k1_tops_1 @ sk_A @ sk_B)
% 0.69/0.90         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.69/0.90      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.69/0.90  thf('73', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['55', '56'])).
% 0.69/0.90  thf('74', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.69/0.90           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['64', '65'])).
% 0.69/0.90  thf('75', plain,
% 0.69/0.90      ((((k3_subset_1 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.69/0.90          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['73', '74'])).
% 0.69/0.90  thf('76', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['55', '56'])).
% 0.69/0.90  thf('77', plain,
% 0.69/0.90      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.90          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('demod', [status(thm)], ['75', '76'])).
% 0.69/0.90  thf('78', plain,
% 0.69/0.90      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.90          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['72', '77'])).
% 0.69/0.90  thf('79', plain,
% 0.69/0.90      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          = (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['69', '70'])).
% 0.69/0.90  thf('80', plain,
% 0.69/0.90      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.90          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['72', '77'])).
% 0.69/0.90  thf(commutativity_k2_xboole_0, axiom,
% 0.69/0.90    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.69/0.90  thf('81', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.69/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.69/0.90  thf('82', plain,
% 0.69/0.90      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.69/0.90          (k1_tops_1 @ sk_A @ sk_B))
% 0.69/0.90          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.69/0.90             (k2_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('demod', [status(thm)], ['62', '71', '78', '79', '80', '81'])).
% 0.69/0.90  thf('83', plain,
% 0.69/0.90      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['57', '58'])).
% 0.69/0.90  thf(t25_subset_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.90       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.69/0.90         ( k2_subset_1 @ A ) ) ))).
% 0.69/0.90  thf('84', plain,
% 0.69/0.90      (![X21 : $i, X22 : $i]:
% 0.69/0.90         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22))
% 0.69/0.90            = (k2_subset_1 @ X21))
% 0.69/0.90          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.69/0.90  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.69/0.90  thf('85', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 0.69/0.90      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.69/0.90  thf('86', plain,
% 0.69/0.90      (![X21 : $i, X22 : $i]:
% 0.69/0.90         (((k4_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X22)) = (X21))
% 0.69/0.90          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.69/0.90      inference('demod', [status(thm)], ['84', '85'])).
% 0.69/0.90  thf('87', plain,
% 0.69/0.90      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.69/0.90          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['83', '86'])).
% 0.69/0.90  thf('88', plain,
% 0.69/0.90      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.90          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['72', '77'])).
% 0.69/0.90  thf('89', plain,
% 0.69/0.90      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.69/0.90          (k1_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('demod', [status(thm)], ['87', '88'])).
% 0.69/0.90  thf('90', plain,
% 0.69/0.90      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.90          = (sk_B)))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['82', '89'])).
% 0.69/0.90  thf('91', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.69/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.69/0.90  thf(idempotence_k2_xboole_0, axiom,
% 0.69/0.90    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.69/0.90  thf('92', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.69/0.90      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.69/0.90  thf(t4_xboole_1, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.69/0.90       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.69/0.90  thf('93', plain,
% 0.69/0.90      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.69/0.90         ((k2_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X9)
% 0.69/0.90           = (k2_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.69/0.90      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.69/0.90  thf('94', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         ((k2_xboole_0 @ X0 @ X1)
% 0.69/0.90           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.69/0.90      inference('sup+', [status(thm)], ['92', '93'])).
% 0.69/0.90  thf('95', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         ((k2_xboole_0 @ X0 @ X1)
% 0.69/0.90           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.69/0.90      inference('sup+', [status(thm)], ['91', '94'])).
% 0.69/0.90  thf('96', plain,
% 0.69/0.90      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.69/0.90          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['90', '95'])).
% 0.69/0.90  thf('97', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.69/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.69/0.90  thf('98', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.69/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.69/0.90  thf('99', plain,
% 0.69/0.90      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.90          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.69/0.90  thf('100', plain,
% 0.69/0.90      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.69/0.90          = (sk_B)))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['82', '89'])).
% 0.69/0.90  thf('101', plain,
% 0.69/0.90      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['99', '100'])).
% 0.69/0.90  thf('102', plain,
% 0.69/0.90      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['40', '101'])).
% 0.69/0.90  thf('103', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(fc1_tops_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.69/0.90         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.69/0.90       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.69/0.90  thf('104', plain,
% 0.69/0.90      (![X30 : $i, X31 : $i]:
% 0.69/0.90         (~ (l1_pre_topc @ X30)
% 0.69/0.90          | ~ (v2_pre_topc @ X30)
% 0.69/0.90          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.69/0.90          | (v4_pre_topc @ (k2_pre_topc @ X30 @ X31) @ X30))),
% 0.69/0.90      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.69/0.90  thf('105', plain,
% 0.69/0.90      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.69/0.90        | ~ (v2_pre_topc @ sk_A)
% 0.69/0.90        | ~ (l1_pre_topc @ sk_A))),
% 0.69/0.90      inference('sup-', [status(thm)], ['103', '104'])).
% 0.69/0.90  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('108', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.69/0.90      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.69/0.90  thf('109', plain,
% 0.69/0.90      (((v4_pre_topc @ sk_B @ sk_A))
% 0.69/0.90         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['102', '108'])).
% 0.69/0.90  thf('110', plain,
% 0.69/0.90      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.69/0.90      inference('split', [status(esa)], ['0'])).
% 0.69/0.90  thf('111', plain,
% 0.69/0.90      (~
% 0.69/0.90       (((k2_tops_1 @ sk_A @ sk_B)
% 0.69/0.90          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.69/0.90             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.69/0.90       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.69/0.90      inference('sup-', [status(thm)], ['109', '110'])).
% 0.69/0.90  thf('112', plain, ($false),
% 0.69/0.90      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '111'])).
% 0.69/0.90  
% 0.69/0.90  % SZS output end Refutation
% 0.69/0.90  
% 0.69/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
