%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bEYoZPnJHw

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:59 EST 2020

% Result     : Theorem 3.88s
% Output     : Refutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 315 expanded)
%              Number of leaves         :   34 ( 106 expanded)
%              Depth                    :   18
%              Number of atoms          : 1441 (3828 expanded)
%              Number of equality atoms :  101 ( 232 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k1_tops_1 @ X37 @ X36 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 @ ( k2_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X25 @ X27 )
        = ( k4_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k2_pre_topc @ X33 @ X32 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X33 ) @ X32 @ ( k2_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('36',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k4_subset_1 @ X23 @ X22 @ X24 )
        = ( k2_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','43'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('47',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('56',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('57',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('67',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','70'])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['44','71'])).

thf('73',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

thf('74',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('81',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('83',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('85',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['76','87'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['75','88'])).

thf('90',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('91',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['74','93'])).

thf('95',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','20'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('97',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','97'])).

thf('99',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','43'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('101',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('103',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
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

thf('106',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_pre_topc @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
       != X28 )
      | ( v4_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('107',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('112',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('114',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','29','30','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bEYoZPnJHw
% 0.17/0.36  % Computer   : n024.cluster.edu
% 0.17/0.36  % Model      : x86_64 x86_64
% 0.17/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.36  % Memory     : 8042.1875MB
% 0.17/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.36  % CPULimit   : 60
% 0.17/0.36  % DateTime   : Tue Dec  1 12:05:36 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 3.88/4.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.88/4.07  % Solved by: fo/fo7.sh
% 3.88/4.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.88/4.07  % done 5586 iterations in 3.584s
% 3.88/4.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.88/4.07  % SZS output start Refutation
% 3.88/4.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.88/4.07  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.88/4.07  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.88/4.07  thf(sk_B_type, type, sk_B: $i).
% 3.88/4.07  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.88/4.07  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.88/4.07  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 3.88/4.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.88/4.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.88/4.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.88/4.07  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.88/4.07  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.88/4.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.88/4.07  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.88/4.07  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.88/4.07  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 3.88/4.07  thf(sk_A_type, type, sk_A: $i).
% 3.88/4.07  thf(t77_tops_1, conjecture,
% 3.88/4.07    (![A:$i]:
% 3.88/4.07     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.88/4.07       ( ![B:$i]:
% 3.88/4.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.88/4.07           ( ( v4_pre_topc @ B @ A ) <=>
% 3.88/4.07             ( ( k2_tops_1 @ A @ B ) =
% 3.88/4.07               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 3.88/4.07  thf(zf_stmt_0, negated_conjecture,
% 3.88/4.07    (~( ![A:$i]:
% 3.88/4.07        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.88/4.07          ( ![B:$i]:
% 3.88/4.07            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.88/4.07              ( ( v4_pre_topc @ B @ A ) <=>
% 3.88/4.07                ( ( k2_tops_1 @ A @ B ) =
% 3.88/4.07                  ( k7_subset_1 @
% 3.88/4.07                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 3.88/4.07    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 3.88/4.07  thf('0', plain,
% 3.88/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07              (k1_tops_1 @ sk_A @ sk_B)))
% 3.88/4.07        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf('1', plain,
% 3.88/4.07      (~
% 3.88/4.07       (((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 3.88/4.07       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 3.88/4.07      inference('split', [status(esa)], ['0'])).
% 3.88/4.07  thf('2', plain,
% 3.88/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07             (k1_tops_1 @ sk_A @ sk_B)))
% 3.88/4.07        | (v4_pre_topc @ sk_B @ sk_A))),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf('3', plain,
% 3.88/4.07      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.88/4.07      inference('split', [status(esa)], ['2'])).
% 3.88/4.07  thf('4', plain,
% 3.88/4.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf(t69_tops_1, axiom,
% 3.88/4.07    (![A:$i]:
% 3.88/4.07     ( ( l1_pre_topc @ A ) =>
% 3.88/4.07       ( ![B:$i]:
% 3.88/4.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.88/4.07           ( ( v4_pre_topc @ B @ A ) =>
% 3.88/4.07             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 3.88/4.07  thf('5', plain,
% 3.88/4.07      (![X34 : $i, X35 : $i]:
% 3.88/4.07         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 3.88/4.07          | (r1_tarski @ (k2_tops_1 @ X35 @ X34) @ X34)
% 3.88/4.07          | ~ (v4_pre_topc @ X34 @ X35)
% 3.88/4.07          | ~ (l1_pre_topc @ X35))),
% 3.88/4.07      inference('cnf', [status(esa)], [t69_tops_1])).
% 3.88/4.07  thf('6', plain,
% 3.88/4.07      ((~ (l1_pre_topc @ sk_A)
% 3.88/4.07        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 3.88/4.07        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 3.88/4.07      inference('sup-', [status(thm)], ['4', '5'])).
% 3.88/4.07  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf('8', plain,
% 3.88/4.07      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 3.88/4.07        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 3.88/4.07      inference('demod', [status(thm)], ['6', '7'])).
% 3.88/4.07  thf('9', plain,
% 3.88/4.07      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 3.88/4.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.88/4.07      inference('sup-', [status(thm)], ['3', '8'])).
% 3.88/4.07  thf(t28_xboole_1, axiom,
% 3.88/4.07    (![A:$i,B:$i]:
% 3.88/4.07     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.88/4.07  thf('10', plain,
% 3.88/4.07      (![X7 : $i, X8 : $i]:
% 3.88/4.07         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 3.88/4.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.88/4.07  thf('11', plain,
% 3.88/4.07      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 3.88/4.07          = (k2_tops_1 @ sk_A @ sk_B)))
% 3.88/4.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.88/4.07      inference('sup-', [status(thm)], ['9', '10'])).
% 3.88/4.07  thf(commutativity_k3_xboole_0, axiom,
% 3.88/4.07    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.88/4.07  thf('12', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.88/4.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.88/4.07  thf('13', plain,
% 3.88/4.07      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.88/4.07          = (k2_tops_1 @ sk_A @ sk_B)))
% 3.88/4.07         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.88/4.07      inference('demod', [status(thm)], ['11', '12'])).
% 3.88/4.07  thf('14', plain,
% 3.88/4.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf(t74_tops_1, axiom,
% 3.88/4.07    (![A:$i]:
% 3.88/4.07     ( ( l1_pre_topc @ A ) =>
% 3.88/4.07       ( ![B:$i]:
% 3.88/4.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.88/4.07           ( ( k1_tops_1 @ A @ B ) =
% 3.88/4.07             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.88/4.07  thf('15', plain,
% 3.88/4.07      (![X36 : $i, X37 : $i]:
% 3.88/4.07         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 3.88/4.07          | ((k1_tops_1 @ X37 @ X36)
% 3.88/4.07              = (k7_subset_1 @ (u1_struct_0 @ X37) @ X36 @ 
% 3.88/4.07                 (k2_tops_1 @ X37 @ X36)))
% 3.88/4.07          | ~ (l1_pre_topc @ X37))),
% 3.88/4.07      inference('cnf', [status(esa)], [t74_tops_1])).
% 3.88/4.07  thf('16', plain,
% 3.88/4.07      ((~ (l1_pre_topc @ sk_A)
% 3.88/4.07        | ((k1_tops_1 @ sk_A @ sk_B)
% 3.88/4.07            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07               (k2_tops_1 @ sk_A @ sk_B))))),
% 3.88/4.07      inference('sup-', [status(thm)], ['14', '15'])).
% 3.88/4.07  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf('18', plain,
% 3.88/4.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf(redefinition_k7_subset_1, axiom,
% 3.88/4.07    (![A:$i,B:$i,C:$i]:
% 3.88/4.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.88/4.07       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 3.88/4.07  thf('19', plain,
% 3.88/4.07      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.88/4.07         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 3.88/4.07          | ((k7_subset_1 @ X26 @ X25 @ X27) = (k4_xboole_0 @ X25 @ X27)))),
% 3.88/4.07      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.88/4.07  thf('20', plain,
% 3.88/4.07      (![X0 : $i]:
% 3.88/4.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.88/4.07           = (k4_xboole_0 @ sk_B @ X0))),
% 3.88/4.07      inference('sup-', [status(thm)], ['18', '19'])).
% 3.88/4.07  thf('21', plain,
% 3.88/4.07      (((k1_tops_1 @ sk_A @ sk_B)
% 3.88/4.07         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.88/4.07      inference('demod', [status(thm)], ['16', '17', '20'])).
% 3.88/4.07  thf(t48_xboole_1, axiom,
% 3.88/4.07    (![A:$i,B:$i]:
% 3.88/4.07     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.88/4.07  thf('22', plain,
% 3.88/4.07      (![X20 : $i, X21 : $i]:
% 3.88/4.07         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 3.88/4.07           = (k3_xboole_0 @ X20 @ X21))),
% 3.88/4.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.88/4.07  thf('23', plain,
% 3.88/4.07      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 3.88/4.07         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.88/4.07      inference('sup+', [status(thm)], ['21', '22'])).
% 3.88/4.07  thf('24', plain,
% 3.88/4.07      (![X0 : $i]:
% 3.88/4.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.88/4.07           = (k4_xboole_0 @ sk_B @ X0))),
% 3.88/4.07      inference('sup-', [status(thm)], ['18', '19'])).
% 3.88/4.07  thf('25', plain,
% 3.88/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07              (k1_tops_1 @ sk_A @ sk_B))))
% 3.88/4.07         <= (~
% 3.88/4.07             (((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('split', [status(esa)], ['0'])).
% 3.88/4.07  thf('26', plain,
% 3.88/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 3.88/4.07         <= (~
% 3.88/4.07             (((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('sup-', [status(thm)], ['24', '25'])).
% 3.88/4.07  thf('27', plain,
% 3.88/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07          != (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 3.88/4.07         <= (~
% 3.88/4.07             (((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('sup-', [status(thm)], ['23', '26'])).
% 3.88/4.07  thf('28', plain,
% 3.88/4.07      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 3.88/4.07         <= (~
% 3.88/4.07             (((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 3.88/4.07             ((v4_pre_topc @ sk_B @ sk_A)))),
% 3.88/4.07      inference('sup-', [status(thm)], ['13', '27'])).
% 3.88/4.07  thf('29', plain,
% 3.88/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 3.88/4.07       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 3.88/4.07      inference('simplify', [status(thm)], ['28'])).
% 3.88/4.07  thf('30', plain,
% 3.88/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 3.88/4.07       ((v4_pre_topc @ sk_B @ sk_A))),
% 3.88/4.07      inference('split', [status(esa)], ['2'])).
% 3.88/4.07  thf('31', plain,
% 3.88/4.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf(t65_tops_1, axiom,
% 3.88/4.07    (![A:$i]:
% 3.88/4.07     ( ( l1_pre_topc @ A ) =>
% 3.88/4.07       ( ![B:$i]:
% 3.88/4.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.88/4.07           ( ( k2_pre_topc @ A @ B ) =
% 3.88/4.07             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.88/4.07  thf('32', plain,
% 3.88/4.07      (![X32 : $i, X33 : $i]:
% 3.88/4.07         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 3.88/4.07          | ((k2_pre_topc @ X33 @ X32)
% 3.88/4.07              = (k4_subset_1 @ (u1_struct_0 @ X33) @ X32 @ 
% 3.88/4.07                 (k2_tops_1 @ X33 @ X32)))
% 3.88/4.07          | ~ (l1_pre_topc @ X33))),
% 3.88/4.07      inference('cnf', [status(esa)], [t65_tops_1])).
% 3.88/4.07  thf('33', plain,
% 3.88/4.07      ((~ (l1_pre_topc @ sk_A)
% 3.88/4.07        | ((k2_pre_topc @ sk_A @ sk_B)
% 3.88/4.07            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07               (k2_tops_1 @ sk_A @ sk_B))))),
% 3.88/4.07      inference('sup-', [status(thm)], ['31', '32'])).
% 3.88/4.07  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf('35', plain,
% 3.88/4.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf(dt_k2_tops_1, axiom,
% 3.88/4.07    (![A:$i,B:$i]:
% 3.88/4.07     ( ( ( l1_pre_topc @ A ) & 
% 3.88/4.07         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.88/4.07       ( m1_subset_1 @
% 3.88/4.07         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.88/4.07  thf('36', plain,
% 3.88/4.07      (![X30 : $i, X31 : $i]:
% 3.88/4.07         (~ (l1_pre_topc @ X30)
% 3.88/4.07          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 3.88/4.07          | (m1_subset_1 @ (k2_tops_1 @ X30 @ X31) @ 
% 3.88/4.07             (k1_zfmisc_1 @ (u1_struct_0 @ X30))))),
% 3.88/4.07      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 3.88/4.07  thf('37', plain,
% 3.88/4.07      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.88/4.07         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.88/4.07        | ~ (l1_pre_topc @ sk_A))),
% 3.88/4.07      inference('sup-', [status(thm)], ['35', '36'])).
% 3.88/4.07  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf('39', plain,
% 3.88/4.07      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.88/4.07        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.88/4.07      inference('demod', [status(thm)], ['37', '38'])).
% 3.88/4.07  thf('40', plain,
% 3.88/4.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf(redefinition_k4_subset_1, axiom,
% 3.88/4.07    (![A:$i,B:$i,C:$i]:
% 3.88/4.07     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.88/4.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.88/4.07       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.88/4.07  thf('41', plain,
% 3.88/4.07      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.88/4.07         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 3.88/4.07          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23))
% 3.88/4.07          | ((k4_subset_1 @ X23 @ X22 @ X24) = (k2_xboole_0 @ X22 @ X24)))),
% 3.88/4.07      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.88/4.07  thf('42', plain,
% 3.88/4.07      (![X0 : $i]:
% 3.88/4.07         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.88/4.07            = (k2_xboole_0 @ sk_B @ X0))
% 3.88/4.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.88/4.07      inference('sup-', [status(thm)], ['40', '41'])).
% 3.88/4.07  thf('43', plain,
% 3.88/4.07      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.88/4.07         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.88/4.07      inference('sup-', [status(thm)], ['39', '42'])).
% 3.88/4.07  thf('44', plain,
% 3.88/4.07      (((k2_pre_topc @ sk_A @ sk_B)
% 3.88/4.07         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.88/4.07      inference('demod', [status(thm)], ['33', '34', '43'])).
% 3.88/4.07  thf(d10_xboole_0, axiom,
% 3.88/4.07    (![A:$i,B:$i]:
% 3.88/4.07     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.88/4.07  thf('45', plain,
% 3.88/4.07      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 3.88/4.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.88/4.07  thf('46', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 3.88/4.07      inference('simplify', [status(thm)], ['45'])).
% 3.88/4.07  thf(t43_xboole_1, axiom,
% 3.88/4.07    (![A:$i,B:$i,C:$i]:
% 3.88/4.07     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 3.88/4.07       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 3.88/4.07  thf('47', plain,
% 3.88/4.07      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.88/4.07         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 3.88/4.07          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 3.88/4.07      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.88/4.07  thf('48', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]:
% 3.88/4.07         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 3.88/4.07      inference('sup-', [status(thm)], ['46', '47'])).
% 3.88/4.07  thf(t12_xboole_1, axiom,
% 3.88/4.07    (![A:$i,B:$i]:
% 3.88/4.07     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.88/4.07  thf('49', plain,
% 3.88/4.07      (![X5 : $i, X6 : $i]:
% 3.88/4.07         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 3.88/4.07      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.88/4.07  thf('50', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]:
% 3.88/4.07         ((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 3.88/4.07           = (X0))),
% 3.88/4.07      inference('sup-', [status(thm)], ['48', '49'])).
% 3.88/4.07  thf('51', plain,
% 3.88/4.07      (![X20 : $i, X21 : $i]:
% 3.88/4.07         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 3.88/4.07           = (k3_xboole_0 @ X20 @ X21))),
% 3.88/4.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.88/4.07  thf(t41_xboole_1, axiom,
% 3.88/4.07    (![A:$i,B:$i,C:$i]:
% 3.88/4.07     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.88/4.07       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.88/4.07  thf('52', plain,
% 3.88/4.07      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.88/4.07         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 3.88/4.07           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 3.88/4.07      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.88/4.07  thf('53', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.88/4.07         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.88/4.07           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 3.88/4.07      inference('sup+', [status(thm)], ['51', '52'])).
% 3.88/4.07  thf('54', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]:
% 3.88/4.07         ((k4_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 3.88/4.07           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 3.88/4.07      inference('sup+', [status(thm)], ['50', '53'])).
% 3.88/4.07  thf('55', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.88/4.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.88/4.07  thf(t36_xboole_1, axiom,
% 3.88/4.07    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.88/4.07  thf('56', plain,
% 3.88/4.07      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 3.88/4.07      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.88/4.07  thf('57', plain,
% 3.88/4.07      (![X5 : $i, X6 : $i]:
% 3.88/4.07         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 3.88/4.07      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.88/4.07  thf('58', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]:
% 3.88/4.07         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 3.88/4.07      inference('sup-', [status(thm)], ['56', '57'])).
% 3.88/4.07  thf('59', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.88/4.07         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.88/4.07           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 3.88/4.07      inference('sup+', [status(thm)], ['51', '52'])).
% 3.88/4.07  thf('60', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]:
% 3.88/4.07         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 3.88/4.07           = (k4_xboole_0 @ X0 @ X0))),
% 3.88/4.07      inference('sup+', [status(thm)], ['58', '59'])).
% 3.88/4.07  thf('61', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.88/4.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.88/4.07  thf('62', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.88/4.07         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.88/4.07           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 3.88/4.07      inference('sup+', [status(thm)], ['51', '52'])).
% 3.88/4.07  thf('63', plain,
% 3.88/4.07      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 3.88/4.07      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.88/4.07  thf('64', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.88/4.07         (r1_tarski @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ X2)),
% 3.88/4.07      inference('sup+', [status(thm)], ['62', '63'])).
% 3.88/4.07  thf('65', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.88/4.07         (r1_tarski @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X0)),
% 3.88/4.07      inference('sup+', [status(thm)], ['61', '64'])).
% 3.88/4.07  thf('66', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 3.88/4.07      inference('sup+', [status(thm)], ['60', '65'])).
% 3.88/4.07  thf(t44_xboole_1, axiom,
% 3.88/4.07    (![A:$i,B:$i,C:$i]:
% 3.88/4.07     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 3.88/4.07       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.88/4.07  thf('67', plain,
% 3.88/4.07      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.88/4.07         ((r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 3.88/4.07          | ~ (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19))),
% 3.88/4.07      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.88/4.07  thf('68', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 3.88/4.07      inference('sup-', [status(thm)], ['66', '67'])).
% 3.88/4.07  thf('69', plain,
% 3.88/4.07      (![X7 : $i, X8 : $i]:
% 3.88/4.07         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 3.88/4.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.88/4.07  thf('70', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]:
% 3.88/4.07         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 3.88/4.07      inference('sup-', [status(thm)], ['68', '69'])).
% 3.88/4.07  thf('71', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]:
% 3.88/4.07         ((k4_xboole_0 @ X1 @ X0)
% 3.88/4.07           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 3.88/4.07      inference('demod', [status(thm)], ['54', '55', '70'])).
% 3.88/4.07  thf('72', plain,
% 3.88/4.07      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.88/4.07         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.88/4.07            (k2_tops_1 @ sk_A @ sk_B)))),
% 3.88/4.07      inference('sup+', [status(thm)], ['44', '71'])).
% 3.88/4.07  thf('73', plain,
% 3.88/4.07      (((k1_tops_1 @ sk_A @ sk_B)
% 3.88/4.07         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.88/4.07      inference('demod', [status(thm)], ['16', '17', '20'])).
% 3.88/4.07  thf('74', plain,
% 3.88/4.07      (((k1_tops_1 @ sk_A @ sk_B)
% 3.88/4.07         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.88/4.07            (k2_tops_1 @ sk_A @ sk_B)))),
% 3.88/4.07      inference('demod', [status(thm)], ['72', '73'])).
% 3.88/4.07  thf('75', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.88/4.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.88/4.07  thf('76', plain,
% 3.88/4.07      (![X20 : $i, X21 : $i]:
% 3.88/4.07         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 3.88/4.07           = (k3_xboole_0 @ X20 @ X21))),
% 3.88/4.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.88/4.07  thf('77', plain,
% 3.88/4.07      (![X0 : $i]:
% 3.88/4.07         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.88/4.07           = (k4_xboole_0 @ sk_B @ X0))),
% 3.88/4.07      inference('sup-', [status(thm)], ['18', '19'])).
% 3.88/4.07  thf('78', plain,
% 3.88/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07             (k1_tops_1 @ sk_A @ sk_B))))
% 3.88/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('split', [status(esa)], ['2'])).
% 3.88/4.07  thf('79', plain,
% 3.88/4.07      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 3.88/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('sup+', [status(thm)], ['77', '78'])).
% 3.88/4.07  thf('80', plain,
% 3.88/4.07      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 3.88/4.07      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.88/4.07  thf('81', plain,
% 3.88/4.07      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 3.88/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('sup+', [status(thm)], ['79', '80'])).
% 3.88/4.07  thf('82', plain,
% 3.88/4.07      (![X7 : $i, X8 : $i]:
% 3.88/4.07         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 3.88/4.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.88/4.07  thf('83', plain,
% 3.88/4.07      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 3.88/4.07          = (k2_tops_1 @ sk_A @ sk_B)))
% 3.88/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('sup-', [status(thm)], ['81', '82'])).
% 3.88/4.07  thf('84', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.88/4.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.88/4.07  thf('85', plain,
% 3.88/4.07      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.88/4.07          = (k2_tops_1 @ sk_A @ sk_B)))
% 3.88/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('demod', [status(thm)], ['83', '84'])).
% 3.88/4.07  thf('86', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.88/4.07         (r1_tarski @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ X2)),
% 3.88/4.07      inference('sup+', [status(thm)], ['62', '63'])).
% 3.88/4.07  thf('87', plain,
% 3.88/4.07      ((![X0 : $i]:
% 3.88/4.07          (r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B))
% 3.88/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('sup+', [status(thm)], ['85', '86'])).
% 3.88/4.07  thf('88', plain,
% 3.88/4.07      ((![X0 : $i]:
% 3.88/4.07          (r1_tarski @ (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B))
% 3.88/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('sup+', [status(thm)], ['76', '87'])).
% 3.88/4.07  thf('89', plain,
% 3.88/4.07      ((![X0 : $i]:
% 3.88/4.07          (r1_tarski @ (k3_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_B))
% 3.88/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('sup+', [status(thm)], ['75', '88'])).
% 3.88/4.07  thf('90', plain,
% 3.88/4.07      (![X20 : $i, X21 : $i]:
% 3.88/4.07         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 3.88/4.07           = (k3_xboole_0 @ X20 @ X21))),
% 3.88/4.07      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.88/4.07  thf('91', plain,
% 3.88/4.07      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.88/4.07         ((r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 3.88/4.07          | ~ (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19))),
% 3.88/4.07      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.88/4.07  thf('92', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.88/4.07         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.88/4.07          | (r1_tarski @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 3.88/4.07      inference('sup-', [status(thm)], ['90', '91'])).
% 3.88/4.07  thf('93', plain,
% 3.88/4.07      ((![X0 : $i]:
% 3.88/4.07          (r1_tarski @ X0 @ 
% 3.88/4.07           (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_B)))
% 3.88/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('sup-', [status(thm)], ['89', '92'])).
% 3.88/4.07  thf('94', plain,
% 3.88/4.07      (((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 3.88/4.07         (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 3.88/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('sup+', [status(thm)], ['74', '93'])).
% 3.88/4.07  thf('95', plain,
% 3.88/4.07      (((k1_tops_1 @ sk_A @ sk_B)
% 3.88/4.07         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.88/4.07      inference('demod', [status(thm)], ['16', '17', '20'])).
% 3.88/4.07  thf('96', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]:
% 3.88/4.07         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 3.88/4.07      inference('sup-', [status(thm)], ['56', '57'])).
% 3.88/4.07  thf('97', plain,
% 3.88/4.07      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 3.88/4.07      inference('sup+', [status(thm)], ['95', '96'])).
% 3.88/4.07  thf('98', plain,
% 3.88/4.07      (((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 3.88/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('demod', [status(thm)], ['94', '97'])).
% 3.88/4.07  thf('99', plain,
% 3.88/4.07      (((k2_pre_topc @ sk_A @ sk_B)
% 3.88/4.07         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.88/4.07      inference('demod', [status(thm)], ['33', '34', '43'])).
% 3.88/4.07  thf('100', plain,
% 3.88/4.07      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 3.88/4.07      inference('sup-', [status(thm)], ['66', '67'])).
% 3.88/4.07  thf('101', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 3.88/4.07      inference('sup+', [status(thm)], ['99', '100'])).
% 3.88/4.07  thf('102', plain,
% 3.88/4.07      (![X2 : $i, X4 : $i]:
% 3.88/4.07         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 3.88/4.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.88/4.07  thf('103', plain,
% 3.88/4.07      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 3.88/4.07        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 3.88/4.07      inference('sup-', [status(thm)], ['101', '102'])).
% 3.88/4.07  thf('104', plain,
% 3.88/4.07      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 3.88/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('sup-', [status(thm)], ['98', '103'])).
% 3.88/4.07  thf('105', plain,
% 3.88/4.07      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf(t52_pre_topc, axiom,
% 3.88/4.07    (![A:$i]:
% 3.88/4.07     ( ( l1_pre_topc @ A ) =>
% 3.88/4.07       ( ![B:$i]:
% 3.88/4.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.88/4.07           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 3.88/4.07             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 3.88/4.07               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 3.88/4.07  thf('106', plain,
% 3.88/4.07      (![X28 : $i, X29 : $i]:
% 3.88/4.07         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.88/4.07          | ~ (v2_pre_topc @ X29)
% 3.88/4.07          | ((k2_pre_topc @ X29 @ X28) != (X28))
% 3.88/4.07          | (v4_pre_topc @ X28 @ X29)
% 3.88/4.07          | ~ (l1_pre_topc @ X29))),
% 3.88/4.07      inference('cnf', [status(esa)], [t52_pre_topc])).
% 3.88/4.07  thf('107', plain,
% 3.88/4.07      ((~ (l1_pre_topc @ sk_A)
% 3.88/4.07        | (v4_pre_topc @ sk_B @ sk_A)
% 3.88/4.07        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 3.88/4.07        | ~ (v2_pre_topc @ sk_A))),
% 3.88/4.07      inference('sup-', [status(thm)], ['105', '106'])).
% 3.88/4.07  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 3.88/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.07  thf('110', plain,
% 3.88/4.07      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 3.88/4.07      inference('demod', [status(thm)], ['107', '108', '109'])).
% 3.88/4.07  thf('111', plain,
% 3.88/4.07      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 3.88/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('sup-', [status(thm)], ['104', '110'])).
% 3.88/4.07  thf('112', plain,
% 3.88/4.07      (((v4_pre_topc @ sk_B @ sk_A))
% 3.88/4.07         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.88/4.07      inference('simplify', [status(thm)], ['111'])).
% 3.88/4.07  thf('113', plain,
% 3.88/4.07      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 3.88/4.07      inference('split', [status(esa)], ['0'])).
% 3.88/4.07  thf('114', plain,
% 3.88/4.07      (~
% 3.88/4.07       (((k2_tops_1 @ sk_A @ sk_B)
% 3.88/4.07          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.88/4.07             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 3.88/4.07       ((v4_pre_topc @ sk_B @ sk_A))),
% 3.88/4.07      inference('sup-', [status(thm)], ['112', '113'])).
% 3.88/4.07  thf('115', plain, ($false),
% 3.88/4.07      inference('sat_resolution*', [status(thm)], ['1', '29', '30', '114'])).
% 3.88/4.07  
% 3.88/4.07  % SZS output end Refutation
% 3.88/4.07  
% 3.88/4.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
