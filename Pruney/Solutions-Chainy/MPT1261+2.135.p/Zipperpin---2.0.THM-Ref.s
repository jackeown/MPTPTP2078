%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pYRnoFw5sP

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:58 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 266 expanded)
%              Number of leaves         :   38 (  92 expanded)
%              Depth                    :   16
%              Number of atoms          : 1389 (3066 expanded)
%              Number of equality atoms :  107 ( 188 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('5',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X35 @ X34 ) @ X34 )
      | ~ ( v4_pre_topc @ X34 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('13',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k1_tops_1 @ X37 @ X36 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 @ ( k2_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('25',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['16','24'])).

thf('26',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','25'])).

thf('27',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('29',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k4_subset_1 @ X20 @ X19 @ X21 )
        = ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k2_pre_topc @ X33 @ X32 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X33 ) @ X32 @ ( k2_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('60',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('62',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('69',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('70',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X18 @ ( k3_subset_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('75',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('77',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('81',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('88',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','92'])).

thf('94',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','93'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('95',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('96',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('98',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['96','105'])).

thf('107',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','106'])).

thf('108',plain,(
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

thf('109',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_pre_topc @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
       != X28 )
      | ( v4_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('110',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['107','113'])).

thf('115',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('117',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pYRnoFw5sP
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.68  % Solved by: fo/fo7.sh
% 0.50/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.68  % done 842 iterations in 0.239s
% 0.50/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.68  % SZS output start Refutation
% 0.50/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.50/0.68  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.50/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.68  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.50/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.68  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.50/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.68  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.50/0.68  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.50/0.68  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.50/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.50/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.50/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.50/0.68  thf(t77_tops_1, conjecture,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.68       ( ![B:$i]:
% 0.50/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.68           ( ( v4_pre_topc @ B @ A ) <=>
% 0.50/0.68             ( ( k2_tops_1 @ A @ B ) =
% 0.50/0.68               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.50/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.68    (~( ![A:$i]:
% 0.50/0.68        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.68          ( ![B:$i]:
% 0.50/0.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.68              ( ( v4_pre_topc @ B @ A ) <=>
% 0.50/0.68                ( ( k2_tops_1 @ A @ B ) =
% 0.50/0.68                  ( k7_subset_1 @
% 0.50/0.68                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.50/0.68    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.50/0.68  thf('0', plain,
% 0.50/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68              (k1_tops_1 @ sk_A @ sk_B)))
% 0.50/0.68        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('1', plain,
% 0.50/0.68      (~
% 0.50/0.68       (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.50/0.68       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.68      inference('split', [status(esa)], ['0'])).
% 0.50/0.68  thf('2', plain,
% 0.50/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68             (k1_tops_1 @ sk_A @ sk_B)))
% 0.50/0.68        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('3', plain,
% 0.50/0.68      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.68      inference('split', [status(esa)], ['2'])).
% 0.50/0.68  thf('4', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(t69_tops_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( l1_pre_topc @ A ) =>
% 0.50/0.68       ( ![B:$i]:
% 0.50/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.68           ( ( v4_pre_topc @ B @ A ) =>
% 0.50/0.68             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.50/0.68  thf('5', plain,
% 0.50/0.68      (![X34 : $i, X35 : $i]:
% 0.50/0.68         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.50/0.68          | (r1_tarski @ (k2_tops_1 @ X35 @ X34) @ X34)
% 0.50/0.68          | ~ (v4_pre_topc @ X34 @ X35)
% 0.50/0.68          | ~ (l1_pre_topc @ X35))),
% 0.50/0.68      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.50/0.68  thf('6', plain,
% 0.50/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.68        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.50/0.68        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.50/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.50/0.68  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('8', plain,
% 0.50/0.68      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.50/0.68        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.50/0.68      inference('demod', [status(thm)], ['6', '7'])).
% 0.50/0.68  thf('9', plain,
% 0.50/0.68      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.50/0.68         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['3', '8'])).
% 0.50/0.68  thf(t3_subset, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.50/0.68  thf('10', plain,
% 0.50/0.68      (![X25 : $i, X27 : $i]:
% 0.50/0.68         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 0.50/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.68  thf('11', plain,
% 0.50/0.68      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.50/0.68         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.68  thf(involutiveness_k3_subset_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.68       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.50/0.68  thf('12', plain,
% 0.50/0.68      (![X17 : $i, X18 : $i]:
% 0.50/0.68         (((k3_subset_1 @ X18 @ (k3_subset_1 @ X18 @ X17)) = (X17))
% 0.50/0.68          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.50/0.68      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.50/0.68  thf('13', plain,
% 0.50/0.68      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.68          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.68         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.50/0.68  thf('14', plain,
% 0.50/0.68      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.50/0.68         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.68  thf(d5_subset_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.68       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.50/0.68  thf('15', plain,
% 0.50/0.68      (![X15 : $i, X16 : $i]:
% 0.50/0.68         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 0.50/0.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.50/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.50/0.68  thf('16', plain,
% 0.50/0.68      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.68          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.50/0.68         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.50/0.68  thf('17', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(t74_tops_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( l1_pre_topc @ A ) =>
% 0.50/0.68       ( ![B:$i]:
% 0.50/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.68           ( ( k1_tops_1 @ A @ B ) =
% 0.50/0.68             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.50/0.68  thf('18', plain,
% 0.50/0.68      (![X36 : $i, X37 : $i]:
% 0.50/0.68         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.50/0.68          | ((k1_tops_1 @ X37 @ X36)
% 0.50/0.68              = (k7_subset_1 @ (u1_struct_0 @ X37) @ X36 @ 
% 0.50/0.68                 (k2_tops_1 @ X37 @ X36)))
% 0.50/0.68          | ~ (l1_pre_topc @ X37))),
% 0.50/0.68      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.50/0.68  thf('19', plain,
% 0.50/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.68        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.50/0.68            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['17', '18'])).
% 0.50/0.68  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('21', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(redefinition_k7_subset_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.68       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.50/0.68  thf('22', plain,
% 0.50/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.50/0.68         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.50/0.68          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 0.50/0.68      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.50/0.68  thf('23', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.50/0.68           = (k4_xboole_0 @ sk_B @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.50/0.68  thf('24', plain,
% 0.50/0.68      (((k1_tops_1 @ sk_A @ sk_B)
% 0.50/0.68         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.50/0.68  thf('25', plain,
% 0.50/0.68      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.50/0.68          = (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.50/0.68         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['16', '24'])).
% 0.50/0.68  thf('26', plain,
% 0.50/0.68      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.50/0.68          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.68         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.68      inference('demod', [status(thm)], ['13', '25'])).
% 0.50/0.68  thf('27', plain,
% 0.50/0.68      (((k1_tops_1 @ sk_A @ sk_B)
% 0.50/0.68         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.50/0.68  thf(t36_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.50/0.68  thf('28', plain,
% 0.50/0.68      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.50/0.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.50/0.68  thf('29', plain,
% 0.50/0.68      (![X25 : $i, X27 : $i]:
% 0.50/0.68         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 0.50/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.68  thf('30', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.68  thf('31', plain,
% 0.50/0.68      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.50/0.68      inference('sup+', [status(thm)], ['27', '30'])).
% 0.50/0.68  thf('32', plain,
% 0.50/0.68      (![X15 : $i, X16 : $i]:
% 0.50/0.68         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 0.50/0.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.50/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.50/0.68  thf('33', plain,
% 0.50/0.68      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.50/0.68         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['31', '32'])).
% 0.50/0.68  thf('34', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.50/0.68           = (k4_xboole_0 @ sk_B @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.50/0.68  thf('35', plain,
% 0.50/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68              (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.68         <= (~
% 0.50/0.68             (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.68      inference('split', [status(esa)], ['0'])).
% 0.50/0.68  thf('36', plain,
% 0.50/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.68         <= (~
% 0.50/0.68             (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['34', '35'])).
% 0.50/0.68  thf('37', plain,
% 0.50/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68          != (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.68         <= (~
% 0.50/0.68             (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['33', '36'])).
% 0.50/0.68  thf('38', plain,
% 0.50/0.68      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.68         <= (~
% 0.50/0.68             (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.50/0.68             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['26', '37'])).
% 0.50/0.68  thf('39', plain,
% 0.50/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.50/0.68       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.68      inference('simplify', [status(thm)], ['38'])).
% 0.50/0.68  thf('40', plain,
% 0.50/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.50/0.68       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.68      inference('split', [status(esa)], ['2'])).
% 0.50/0.68  thf('41', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(dt_k2_tops_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( ( l1_pre_topc @ A ) & 
% 0.50/0.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.50/0.68       ( m1_subset_1 @
% 0.50/0.68         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.50/0.68  thf('42', plain,
% 0.50/0.68      (![X30 : $i, X31 : $i]:
% 0.50/0.68         (~ (l1_pre_topc @ X30)
% 0.50/0.68          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.50/0.68          | (m1_subset_1 @ (k2_tops_1 @ X30 @ X31) @ 
% 0.50/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X30))))),
% 0.50/0.68      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.50/0.68  thf('43', plain,
% 0.50/0.68      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.50/0.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.50/0.68      inference('sup-', [status(thm)], ['41', '42'])).
% 0.50/0.68  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('45', plain,
% 0.50/0.68      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.50/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.68      inference('demod', [status(thm)], ['43', '44'])).
% 0.50/0.68  thf('46', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(redefinition_k4_subset_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.50/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.50/0.68       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.50/0.68  thf('47', plain,
% 0.50/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.50/0.68         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.50/0.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.50/0.68          | ((k4_subset_1 @ X20 @ X19 @ X21) = (k2_xboole_0 @ X19 @ X21)))),
% 0.50/0.68      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.50/0.68  thf('48', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.50/0.68            = (k2_xboole_0 @ sk_B @ X0))
% 0.50/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['46', '47'])).
% 0.50/0.68  thf('49', plain,
% 0.50/0.68      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.68         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['45', '48'])).
% 0.50/0.68  thf('50', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(t65_tops_1, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( l1_pre_topc @ A ) =>
% 0.50/0.68       ( ![B:$i]:
% 0.50/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.68           ( ( k2_pre_topc @ A @ B ) =
% 0.50/0.68             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.50/0.68  thf('51', plain,
% 0.50/0.68      (![X32 : $i, X33 : $i]:
% 0.50/0.68         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.50/0.68          | ((k2_pre_topc @ X33 @ X32)
% 0.50/0.68              = (k4_subset_1 @ (u1_struct_0 @ X33) @ X32 @ 
% 0.50/0.68                 (k2_tops_1 @ X33 @ X32)))
% 0.50/0.68          | ~ (l1_pre_topc @ X33))),
% 0.50/0.68      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.50/0.68  thf('52', plain,
% 0.50/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.68        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.50/0.68            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['50', '51'])).
% 0.50/0.68  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf('54', plain,
% 0.50/0.68      (((k2_pre_topc @ sk_A @ sk_B)
% 0.50/0.68         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('demod', [status(thm)], ['52', '53'])).
% 0.50/0.68  thf('55', plain,
% 0.50/0.68      (((k2_pre_topc @ sk_A @ sk_B)
% 0.50/0.68         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['49', '54'])).
% 0.50/0.68  thf('56', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.50/0.68           = (k4_xboole_0 @ sk_B @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.50/0.68  thf('57', plain,
% 0.50/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68             (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.68      inference('split', [status(esa)], ['2'])).
% 0.50/0.68  thf('58', plain,
% 0.50/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['56', '57'])).
% 0.50/0.68  thf('59', plain,
% 0.50/0.68      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.50/0.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.50/0.68  thf('60', plain,
% 0.50/0.68      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.50/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['58', '59'])).
% 0.50/0.68  thf(t28_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.50/0.68  thf('61', plain,
% 0.50/0.68      (![X7 : $i, X8 : $i]:
% 0.50/0.68         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.50/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.68  thf('62', plain,
% 0.50/0.68      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.50/0.68          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.50/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.50/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.50/0.68  thf('63', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.68  thf('64', plain,
% 0.50/0.68      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.68          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.50/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.68      inference('demod', [status(thm)], ['62', '63'])).
% 0.50/0.68  thf('65', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.68  thf(t100_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.68  thf('66', plain,
% 0.50/0.68      (![X5 : $i, X6 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X5 @ X6)
% 0.50/0.68           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.68  thf('67', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X0 @ X1)
% 0.50/0.68           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['65', '66'])).
% 0.50/0.68  thf('68', plain,
% 0.50/0.68      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.50/0.68          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.50/0.68             (k2_tops_1 @ sk_A @ sk_B))))
% 0.50/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['64', '67'])).
% 0.50/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.50/0.68  thf('69', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.50/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.68  thf('70', plain,
% 0.50/0.68      (![X25 : $i, X27 : $i]:
% 0.50/0.68         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 0.50/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.68  thf('71', plain,
% 0.50/0.68      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['69', '70'])).
% 0.50/0.68  thf('72', plain,
% 0.50/0.68      (![X17 : $i, X18 : $i]:
% 0.50/0.68         (((k3_subset_1 @ X18 @ (k3_subset_1 @ X18 @ X17)) = (X17))
% 0.50/0.68          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.50/0.68      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.50/0.68  thf('73', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['71', '72'])).
% 0.50/0.68  thf('74', plain,
% 0.50/0.68      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['69', '70'])).
% 0.50/0.68  thf('75', plain,
% 0.50/0.68      (![X15 : $i, X16 : $i]:
% 0.50/0.68         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 0.50/0.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.50/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.50/0.68  thf('76', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['74', '75'])).
% 0.50/0.68  thf(t3_boole, axiom,
% 0.50/0.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.50/0.68  thf('77', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.50/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.50/0.68  thf('78', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['76', '77'])).
% 0.50/0.68  thf('79', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['73', '78'])).
% 0.50/0.68  thf('80', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.50/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.50/0.68  thf('81', plain,
% 0.50/0.68      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.50/0.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.50/0.68  thf('82', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.50/0.68      inference('sup+', [status(thm)], ['80', '81'])).
% 0.50/0.68  thf('83', plain,
% 0.50/0.68      (![X7 : $i, X8 : $i]:
% 0.50/0.68         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.50/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.68  thf('84', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['82', '83'])).
% 0.50/0.68  thf('85', plain,
% 0.50/0.68      (![X5 : $i, X6 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X5 @ X6)
% 0.50/0.68           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.68  thf('86', plain,
% 0.50/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['84', '85'])).
% 0.50/0.68  thf('87', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.50/0.68      inference('sup+', [status(thm)], ['80', '81'])).
% 0.50/0.68  thf('88', plain,
% 0.50/0.68      (![X25 : $i, X27 : $i]:
% 0.50/0.68         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 0.50/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.68  thf('89', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['87', '88'])).
% 0.50/0.68  thf('90', plain,
% 0.50/0.68      (![X15 : $i, X16 : $i]:
% 0.50/0.68         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 0.50/0.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.50/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.50/0.68  thf('91', plain,
% 0.50/0.68      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['89', '90'])).
% 0.50/0.68  thf('92', plain,
% 0.50/0.68      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['86', '91'])).
% 0.50/0.68  thf('93', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.68      inference('demod', [status(thm)], ['79', '92'])).
% 0.50/0.68  thf('94', plain,
% 0.50/0.68      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.50/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.68      inference('demod', [status(thm)], ['68', '93'])).
% 0.50/0.68  thf(t98_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.50/0.68  thf('95', plain,
% 0.50/0.68      (![X13 : $i, X14 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ X13 @ X14)
% 0.50/0.68           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.50/0.68  thf('96', plain,
% 0.50/0.68      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.68          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.50/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['94', '95'])).
% 0.50/0.68  thf('97', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.50/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.68  thf('98', plain,
% 0.50/0.68      (![X7 : $i, X8 : $i]:
% 0.50/0.68         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.50/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.68  thf('99', plain,
% 0.50/0.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.50/0.68      inference('sup-', [status(thm)], ['97', '98'])).
% 0.50/0.68  thf('100', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.68  thf('101', plain,
% 0.50/0.68      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['99', '100'])).
% 0.50/0.68  thf('102', plain,
% 0.50/0.68      (![X5 : $i, X6 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X5 @ X6)
% 0.50/0.68           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.68  thf('103', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['101', '102'])).
% 0.50/0.68  thf('104', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.50/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.50/0.68  thf('105', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['103', '104'])).
% 0.50/0.68  thf('106', plain,
% 0.50/0.68      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.50/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.68      inference('demod', [status(thm)], ['96', '105'])).
% 0.50/0.68  thf('107', plain,
% 0.50/0.68      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.50/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['55', '106'])).
% 0.50/0.68  thf('108', plain,
% 0.50/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(t52_pre_topc, axiom,
% 0.50/0.68    (![A:$i]:
% 0.50/0.68     ( ( l1_pre_topc @ A ) =>
% 0.50/0.68       ( ![B:$i]:
% 0.50/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.68           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.50/0.68             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.50/0.68               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.50/0.68  thf('109', plain,
% 0.50/0.68      (![X28 : $i, X29 : $i]:
% 0.50/0.68         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.50/0.68          | ~ (v2_pre_topc @ X29)
% 0.50/0.68          | ((k2_pre_topc @ X29 @ X28) != (X28))
% 0.50/0.68          | (v4_pre_topc @ X28 @ X29)
% 0.50/0.68          | ~ (l1_pre_topc @ X29))),
% 0.50/0.69      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.50/0.69  thf('110', plain,
% 0.50/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.69        | (v4_pre_topc @ sk_B @ sk_A)
% 0.50/0.69        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.50/0.69        | ~ (v2_pre_topc @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['108', '109'])).
% 0.50/0.69  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('112', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('113', plain,
% 0.50/0.69      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.50/0.69      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.50/0.69  thf('114', plain,
% 0.50/0.69      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.50/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.69      inference('sup-', [status(thm)], ['107', '113'])).
% 0.50/0.69  thf('115', plain,
% 0.50/0.69      (((v4_pre_topc @ sk_B @ sk_A))
% 0.50/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.69      inference('simplify', [status(thm)], ['114'])).
% 0.50/0.69  thf('116', plain,
% 0.50/0.69      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.69      inference('split', [status(esa)], ['0'])).
% 0.50/0.69  thf('117', plain,
% 0.50/0.69      (~
% 0.50/0.69       (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.69             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.50/0.69       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['115', '116'])).
% 0.50/0.69  thf('118', plain, ($false),
% 0.50/0.69      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '117'])).
% 0.50/0.69  
% 0.50/0.69  % SZS output end Refutation
% 0.50/0.69  
% 0.50/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
