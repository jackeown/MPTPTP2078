%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7q9AselsGY

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:03 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 208 expanded)
%              Number of leaves         :   35 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          : 1101 (2642 expanded)
%              Number of equality atoms :   77 ( 147 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X34 @ X33 ) @ X33 )
      | ~ ( v4_pre_topc @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
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
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
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
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k1_tops_1 @ X36 @ X35 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 @ ( k2_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('29',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k4_subset_1 @ X19 @ X18 @ X20 )
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_pre_topc @ X32 @ X31 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 @ ( k2_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('60',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('64',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('65',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('70',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','71'])).

thf('73',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','72'])).

thf('74',plain,(
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

thf('75',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_pre_topc @ X28 )
      | ( ( k2_pre_topc @ X28 @ X27 )
       != X27 )
      | ( v4_pre_topc @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7q9AselsGY
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:17:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 539 iterations in 0.180s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.45/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.45/0.63  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.45/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.45/0.63  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.63  thf(t77_tops_1, conjecture,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( v4_pre_topc @ B @ A ) <=>
% 0.45/0.63             ( ( k2_tops_1 @ A @ B ) =
% 0.45/0.63               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i]:
% 0.45/0.63        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63          ( ![B:$i]:
% 0.45/0.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63              ( ( v4_pre_topc @ B @ A ) <=>
% 0.45/0.63                ( ( k2_tops_1 @ A @ B ) =
% 0.45/0.63                  ( k7_subset_1 @
% 0.45/0.63                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63              (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.63        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (~
% 0.45/0.63       (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.63       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63             (k1_tops_1 @ sk_A @ sk_B)))
% 0.45/0.63        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('split', [status(esa)], ['2'])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t69_tops_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( v4_pre_topc @ B @ A ) =>
% 0.45/0.63             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X33 : $i, X34 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.45/0.63          | (r1_tarski @ (k2_tops_1 @ X34 @ X33) @ X33)
% 0.45/0.63          | ~ (v4_pre_topc @ X33 @ X34)
% 0.45/0.63          | ~ (l1_pre_topc @ X34))),
% 0.45/0.63      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.45/0.63        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.63  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.45/0.63        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.45/0.63         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['3', '8'])).
% 0.45/0.63  thf(t3_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      (![X24 : $i, X26 : $i]:
% 0.45/0.63         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.45/0.63         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.63  thf(involutiveness_k3_subset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (![X16 : $i, X17 : $i]:
% 0.45/0.63         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 0.45/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.45/0.63      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.63          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.63         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.45/0.63         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.63  thf(d5_subset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X14 : $i, X15 : $i]:
% 0.45/0.63         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.45/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.63          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t74_tops_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( k1_tops_1 @ A @ B ) =
% 0.45/0.63             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      (![X35 : $i, X36 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.45/0.63          | ((k1_tops_1 @ X36 @ X35)
% 0.45/0.63              = (k7_subset_1 @ (u1_struct_0 @ X36) @ X35 @ 
% 0.45/0.63                 (k2_tops_1 @ X36 @ X35)))
% 0.45/0.63          | ~ (l1_pre_topc @ X36))),
% 0.45/0.63      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.63            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.63  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(redefinition_k7_subset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.45/0.63          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.63           = (k4_xboole_0 @ sk_B @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.63         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['16', '24'])).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.63          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.63         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['13', '25'])).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      (((k1_tops_1 @ sk_A @ sk_B)
% 0.45/0.63         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.45/0.63  thf(t36_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.45/0.63      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      (![X24 : $i, X26 : $i]:
% 0.45/0.63         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.45/0.63      inference('sup+', [status(thm)], ['27', '30'])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      (![X14 : $i, X15 : $i]:
% 0.45/0.63         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.45/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.45/0.63         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.63           = (k4_xboole_0 @ sk_B @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.63  thf('35', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63              (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= (~
% 0.45/0.63             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= (~
% 0.45/0.63             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          != (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= (~
% 0.45/0.63             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['33', '36'])).
% 0.45/0.63  thf('38', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.45/0.63         <= (~
% 0.45/0.63             (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.45/0.63             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['26', '37'])).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.63       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('simplify', [status(thm)], ['38'])).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.63       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('split', [status(esa)], ['2'])).
% 0.45/0.63  thf('41', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(dt_k2_tops_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( l1_pre_topc @ A ) & 
% 0.45/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.63       ( m1_subset_1 @
% 0.45/0.63         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.63  thf('42', plain,
% 0.45/0.63      (![X29 : $i, X30 : $i]:
% 0.45/0.63         (~ (l1_pre_topc @ X29)
% 0.45/0.63          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.45/0.63          | (m1_subset_1 @ (k2_tops_1 @ X29 @ X30) @ 
% 0.45/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.63  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('45', plain,
% 0.45/0.63      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.45/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.45/0.63  thf('46', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(redefinition_k4_subset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.45/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.63       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.45/0.63  thf('47', plain,
% 0.45/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.45/0.63          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19))
% 0.45/0.63          | ((k4_subset_1 @ X19 @ X18 @ X20) = (k2_xboole_0 @ X18 @ X20)))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.45/0.63  thf('48', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.63            = (k2_xboole_0 @ sk_B @ X0))
% 0.45/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.63  thf('49', plain,
% 0.45/0.63      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.63         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['45', '48'])).
% 0.45/0.63  thf('50', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t65_tops_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( k2_pre_topc @ A @ B ) =
% 0.45/0.63             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.63  thf('51', plain,
% 0.45/0.63      (![X31 : $i, X32 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.45/0.63          | ((k2_pre_topc @ X32 @ X31)
% 0.45/0.63              = (k4_subset_1 @ (u1_struct_0 @ X32) @ X31 @ 
% 0.45/0.63                 (k2_tops_1 @ X32 @ X31)))
% 0.45/0.63          | ~ (l1_pre_topc @ X32))),
% 0.45/0.63      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.45/0.63  thf('52', plain,
% 0.45/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.45/0.63            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.63  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('54', plain,
% 0.45/0.63      (((k2_pre_topc @ sk_A @ sk_B)
% 0.45/0.63         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.45/0.63  thf('55', plain,
% 0.45/0.63      (((k2_pre_topc @ sk_A @ sk_B)
% 0.45/0.63         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['49', '54'])).
% 0.45/0.63  thf('56', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.45/0.63           = (k4_xboole_0 @ sk_B @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.63  thf('57', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63             (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('split', [status(esa)], ['2'])).
% 0.45/0.63  thf('58', plain,
% 0.45/0.63      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['56', '57'])).
% 0.45/0.63  thf('59', plain,
% 0.45/0.63      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.45/0.63      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.45/0.63  thf(l32_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.63  thf('60', plain,
% 0.45/0.63      (![X0 : $i, X2 : $i]:
% 0.45/0.63         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.63  thf('61', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['59', '60'])).
% 0.45/0.63  thf('62', plain,
% 0.45/0.63      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['58', '61'])).
% 0.45/0.63  thf(t98_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.63  thf('63', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ X12 @ X13)
% 0.45/0.63           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.63  thf('64', plain,
% 0.45/0.63      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.45/0.63          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['62', '63'])).
% 0.45/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.63  thf('65', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.45/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.63  thf('66', plain,
% 0.45/0.63      (![X0 : $i, X2 : $i]:
% 0.45/0.63         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.63      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.63  thf('67', plain,
% 0.45/0.63      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.63  thf('68', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ X12 @ X13)
% 0.45/0.63           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.63  thf('69', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['67', '68'])).
% 0.45/0.63  thf(t1_boole, axiom,
% 0.45/0.63    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.63  thf('70', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [t1_boole])).
% 0.45/0.63  thf('71', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['69', '70'])).
% 0.45/0.63  thf('72', plain,
% 0.45/0.63      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('demod', [status(thm)], ['64', '71'])).
% 0.45/0.63  thf('73', plain,
% 0.45/0.63      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['55', '72'])).
% 0.45/0.63  thf('74', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t52_pre_topc, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.63           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.45/0.63             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.45/0.63               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.45/0.63  thf('75', plain,
% 0.45/0.63      (![X27 : $i, X28 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.45/0.63          | ~ (v2_pre_topc @ X28)
% 0.45/0.63          | ((k2_pre_topc @ X28 @ X27) != (X27))
% 0.45/0.63          | (v4_pre_topc @ X27 @ X28)
% 0.45/0.63          | ~ (l1_pre_topc @ X28))),
% 0.45/0.63      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.45/0.63  thf('76', plain,
% 0.45/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (v4_pre_topc @ sk_B @ sk_A)
% 0.45/0.63        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.45/0.63        | ~ (v2_pre_topc @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.63  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('79', plain,
% 0.45/0.63      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.45/0.63      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.45/0.63  thf('80', plain,
% 0.45/0.63      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['73', '79'])).
% 0.45/0.63  thf('81', plain,
% 0.45/0.63      (((v4_pre_topc @ sk_B @ sk_A))
% 0.45/0.63         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.45/0.63      inference('simplify', [status(thm)], ['80'])).
% 0.45/0.63  thf('82', plain,
% 0.45/0.63      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('83', plain,
% 0.45/0.63      (~
% 0.45/0.63       (((k2_tops_1 @ sk_A @ sk_B)
% 0.45/0.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.63             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.45/0.63       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['81', '82'])).
% 0.45/0.63  thf('84', plain, ($false),
% 0.45/0.63      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '83'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
