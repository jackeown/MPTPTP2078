%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.76sbdCw4NU

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:58 EST 2020

% Result     : Theorem 5.24s
% Output     : Refutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 637 expanded)
%              Number of leaves         :   34 ( 215 expanded)
%              Depth                    :   23
%              Number of atoms          : 1475 (5588 expanded)
%              Number of equality atoms :  125 ( 468 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X31 @ X30 ) @ X30 )
      | ~ ( v4_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k1_tops_1 @ X33 @ X32 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X33 ) @ X32 @ ( k2_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
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
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('32',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','63'])).

thf('65',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('70',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['71','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','90'])).

thf('92',plain,
    ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['37','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('94',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k2_pre_topc @ X29 @ X28 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 @ ( k2_tops_1 @ X29 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('98',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('99',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('103',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k4_subset_1 @ X19 @ X18 @ X20 )
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','96','105'])).

thf('107',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['92','106'])).

thf('108',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('109',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['71','75'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('112',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','96','105'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('114',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['112','117'])).

thf('119',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('120',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['71','75'])).

thf('122',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['109','110','111','122'])).

thf('124',plain,(
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

thf('125',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v2_pre_topc @ X25 )
      | ( ( k2_pre_topc @ X25 @ X24 )
       != X24 )
      | ( v4_pre_topc @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('126',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['123','129'])).

thf('131',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('133',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','29','30','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.76sbdCw4NU
% 0.15/0.35  % Computer   : n013.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:28:10 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 5.24/5.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.24/5.45  % Solved by: fo/fo7.sh
% 5.24/5.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.24/5.45  % done 8553 iterations in 4.984s
% 5.24/5.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.24/5.45  % SZS output start Refutation
% 5.24/5.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.24/5.45  thf(sk_B_type, type, sk_B: $i).
% 5.24/5.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.24/5.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.24/5.45  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 5.24/5.45  thf(sk_A_type, type, sk_A: $i).
% 5.24/5.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.24/5.45  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 5.24/5.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.24/5.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.24/5.45  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 5.24/5.45  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.24/5.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.24/5.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.24/5.45  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 5.24/5.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.24/5.45  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 5.24/5.45  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 5.24/5.45  thf(t77_tops_1, conjecture,
% 5.24/5.45    (![A:$i]:
% 5.24/5.45     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.24/5.45       ( ![B:$i]:
% 5.24/5.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.24/5.45           ( ( v4_pre_topc @ B @ A ) <=>
% 5.24/5.45             ( ( k2_tops_1 @ A @ B ) =
% 5.24/5.45               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 5.24/5.45  thf(zf_stmt_0, negated_conjecture,
% 5.24/5.45    (~( ![A:$i]:
% 5.24/5.45        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.24/5.45          ( ![B:$i]:
% 5.24/5.45            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.24/5.45              ( ( v4_pre_topc @ B @ A ) <=>
% 5.24/5.45                ( ( k2_tops_1 @ A @ B ) =
% 5.24/5.45                  ( k7_subset_1 @
% 5.24/5.45                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 5.24/5.45    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 5.24/5.45  thf('0', plain,
% 5.24/5.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45              (k1_tops_1 @ sk_A @ sk_B)))
% 5.24/5.45        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.24/5.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.45  thf('1', plain,
% 5.24/5.45      (~
% 5.24/5.45       (((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 5.24/5.45       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 5.24/5.45      inference('split', [status(esa)], ['0'])).
% 5.24/5.45  thf('2', plain,
% 5.24/5.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45             (k1_tops_1 @ sk_A @ sk_B)))
% 5.24/5.45        | (v4_pre_topc @ sk_B @ sk_A))),
% 5.24/5.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.45  thf('3', plain,
% 5.24/5.45      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.24/5.45      inference('split', [status(esa)], ['2'])).
% 5.24/5.45  thf('4', plain,
% 5.24/5.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.24/5.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.45  thf(t69_tops_1, axiom,
% 5.24/5.45    (![A:$i]:
% 5.24/5.45     ( ( l1_pre_topc @ A ) =>
% 5.24/5.45       ( ![B:$i]:
% 5.24/5.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.24/5.45           ( ( v4_pre_topc @ B @ A ) =>
% 5.24/5.45             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 5.24/5.45  thf('5', plain,
% 5.24/5.45      (![X30 : $i, X31 : $i]:
% 5.24/5.45         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 5.24/5.45          | (r1_tarski @ (k2_tops_1 @ X31 @ X30) @ X30)
% 5.24/5.45          | ~ (v4_pre_topc @ X30 @ X31)
% 5.24/5.45          | ~ (l1_pre_topc @ X31))),
% 5.24/5.45      inference('cnf', [status(esa)], [t69_tops_1])).
% 5.24/5.45  thf('6', plain,
% 5.24/5.45      ((~ (l1_pre_topc @ sk_A)
% 5.24/5.45        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 5.24/5.45        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 5.24/5.45      inference('sup-', [status(thm)], ['4', '5'])).
% 5.24/5.45  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 5.24/5.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.45  thf('8', plain,
% 5.24/5.45      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 5.24/5.45        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 5.24/5.45      inference('demod', [status(thm)], ['6', '7'])).
% 5.24/5.45  thf('9', plain,
% 5.24/5.45      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 5.24/5.45         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.24/5.45      inference('sup-', [status(thm)], ['3', '8'])).
% 5.24/5.45  thf(t28_xboole_1, axiom,
% 5.24/5.45    (![A:$i,B:$i]:
% 5.24/5.45     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.24/5.45  thf('10', plain,
% 5.24/5.45      (![X9 : $i, X10 : $i]:
% 5.24/5.45         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 5.24/5.45      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.24/5.45  thf('11', plain,
% 5.24/5.45      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 5.24/5.45          = (k2_tops_1 @ sk_A @ sk_B)))
% 5.24/5.45         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.24/5.45      inference('sup-', [status(thm)], ['9', '10'])).
% 5.24/5.45  thf(commutativity_k3_xboole_0, axiom,
% 5.24/5.45    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.24/5.45  thf('12', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.24/5.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.24/5.45  thf('13', plain,
% 5.24/5.45      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 5.24/5.45          = (k2_tops_1 @ sk_A @ sk_B)))
% 5.24/5.45         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.24/5.45      inference('demod', [status(thm)], ['11', '12'])).
% 5.24/5.45  thf('14', plain,
% 5.24/5.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.24/5.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.45  thf(t74_tops_1, axiom,
% 5.24/5.45    (![A:$i]:
% 5.24/5.45     ( ( l1_pre_topc @ A ) =>
% 5.24/5.45       ( ![B:$i]:
% 5.24/5.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.24/5.45           ( ( k1_tops_1 @ A @ B ) =
% 5.24/5.45             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 5.24/5.45  thf('15', plain,
% 5.24/5.45      (![X32 : $i, X33 : $i]:
% 5.24/5.45         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 5.24/5.45          | ((k1_tops_1 @ X33 @ X32)
% 5.24/5.45              = (k7_subset_1 @ (u1_struct_0 @ X33) @ X32 @ 
% 5.24/5.45                 (k2_tops_1 @ X33 @ X32)))
% 5.24/5.45          | ~ (l1_pre_topc @ X33))),
% 5.24/5.45      inference('cnf', [status(esa)], [t74_tops_1])).
% 5.24/5.45  thf('16', plain,
% 5.24/5.45      ((~ (l1_pre_topc @ sk_A)
% 5.24/5.45        | ((k1_tops_1 @ sk_A @ sk_B)
% 5.24/5.45            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45               (k2_tops_1 @ sk_A @ sk_B))))),
% 5.24/5.45      inference('sup-', [status(thm)], ['14', '15'])).
% 5.24/5.45  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 5.24/5.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.45  thf('18', plain,
% 5.24/5.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.24/5.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.45  thf(redefinition_k7_subset_1, axiom,
% 5.24/5.45    (![A:$i,B:$i,C:$i]:
% 5.24/5.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.24/5.45       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 5.24/5.45  thf('19', plain,
% 5.24/5.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 5.24/5.45         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 5.24/5.45          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 5.24/5.45      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 5.24/5.45  thf('20', plain,
% 5.24/5.45      (![X0 : $i]:
% 5.24/5.45         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 5.24/5.45           = (k4_xboole_0 @ sk_B @ X0))),
% 5.24/5.45      inference('sup-', [status(thm)], ['18', '19'])).
% 5.24/5.45  thf('21', plain,
% 5.24/5.45      (((k1_tops_1 @ sk_A @ sk_B)
% 5.24/5.45         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.24/5.45      inference('demod', [status(thm)], ['16', '17', '20'])).
% 5.24/5.45  thf(t48_xboole_1, axiom,
% 5.24/5.45    (![A:$i,B:$i]:
% 5.24/5.45     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.24/5.45  thf('22', plain,
% 5.24/5.45      (![X16 : $i, X17 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.24/5.45           = (k3_xboole_0 @ X16 @ X17))),
% 5.24/5.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.24/5.45  thf('23', plain,
% 5.24/5.45      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.24/5.45         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.24/5.45      inference('sup+', [status(thm)], ['21', '22'])).
% 5.24/5.45  thf('24', plain,
% 5.24/5.45      (![X0 : $i]:
% 5.24/5.45         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 5.24/5.45           = (k4_xboole_0 @ sk_B @ X0))),
% 5.24/5.45      inference('sup-', [status(thm)], ['18', '19'])).
% 5.24/5.45  thf('25', plain,
% 5.24/5.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45              (k1_tops_1 @ sk_A @ sk_B))))
% 5.24/5.45         <= (~
% 5.24/5.45             (((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.24/5.45      inference('split', [status(esa)], ['0'])).
% 5.24/5.45  thf('26', plain,
% 5.24/5.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 5.24/5.45         <= (~
% 5.24/5.45             (((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.24/5.45      inference('sup-', [status(thm)], ['24', '25'])).
% 5.24/5.45  thf('27', plain,
% 5.24/5.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45          != (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 5.24/5.45         <= (~
% 5.24/5.45             (((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.24/5.45      inference('sup-', [status(thm)], ['23', '26'])).
% 5.24/5.45  thf('28', plain,
% 5.24/5.45      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 5.24/5.45         <= (~
% 5.24/5.45             (((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 5.24/5.45             ((v4_pre_topc @ sk_B @ sk_A)))),
% 5.24/5.45      inference('sup-', [status(thm)], ['13', '27'])).
% 5.24/5.45  thf('29', plain,
% 5.24/5.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 5.24/5.45       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 5.24/5.45      inference('simplify', [status(thm)], ['28'])).
% 5.24/5.45  thf('30', plain,
% 5.24/5.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 5.24/5.45       ((v4_pre_topc @ sk_B @ sk_A))),
% 5.24/5.45      inference('split', [status(esa)], ['2'])).
% 5.24/5.45  thf('31', plain,
% 5.24/5.45      (![X0 : $i]:
% 5.24/5.45         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 5.24/5.45           = (k4_xboole_0 @ sk_B @ X0))),
% 5.24/5.45      inference('sup-', [status(thm)], ['18', '19'])).
% 5.24/5.45  thf('32', plain,
% 5.24/5.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45             (k1_tops_1 @ sk_A @ sk_B))))
% 5.24/5.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.24/5.45      inference('split', [status(esa)], ['2'])).
% 5.24/5.45  thf('33', plain,
% 5.24/5.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 5.24/5.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.24/5.45      inference('sup+', [status(thm)], ['31', '32'])).
% 5.24/5.45  thf(t36_xboole_1, axiom,
% 5.24/5.45    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 5.24/5.45  thf('34', plain,
% 5.24/5.45      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 5.24/5.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.24/5.45  thf(t12_xboole_1, axiom,
% 5.24/5.45    (![A:$i,B:$i]:
% 5.24/5.45     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 5.24/5.45  thf('35', plain,
% 5.24/5.45      (![X6 : $i, X7 : $i]:
% 5.24/5.45         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 5.24/5.45      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.24/5.45  thf('36', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 5.24/5.45      inference('sup-', [status(thm)], ['34', '35'])).
% 5.24/5.45  thf('37', plain,
% 5.24/5.45      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B)))
% 5.24/5.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.24/5.45      inference('sup+', [status(thm)], ['33', '36'])).
% 5.24/5.45  thf('38', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 5.24/5.45      inference('sup-', [status(thm)], ['34', '35'])).
% 5.24/5.45  thf(t41_xboole_1, axiom,
% 5.24/5.45    (![A:$i,B:$i,C:$i]:
% 5.24/5.45     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 5.24/5.45       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 5.24/5.45  thf('39', plain,
% 5.24/5.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 5.24/5.45           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 5.24/5.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.24/5.45  thf('40', plain,
% 5.24/5.45      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 5.24/5.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.24/5.45  thf('41', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.24/5.45         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 5.24/5.45          (k4_xboole_0 @ X2 @ X1))),
% 5.24/5.45      inference('sup+', [status(thm)], ['39', '40'])).
% 5.24/5.45  thf('42', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.24/5.45         (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ 
% 5.24/5.45          (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 5.24/5.45      inference('sup+', [status(thm)], ['38', '41'])).
% 5.24/5.45  thf('43', plain,
% 5.24/5.45      (![X16 : $i, X17 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.24/5.45           = (k3_xboole_0 @ X16 @ X17))),
% 5.24/5.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.24/5.45  thf('44', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 5.24/5.45      inference('sup-', [status(thm)], ['34', '35'])).
% 5.24/5.45  thf(t1_boole, axiom,
% 5.24/5.45    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.24/5.45  thf('45', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 5.24/5.45      inference('cnf', [status(esa)], [t1_boole])).
% 5.24/5.45  thf('46', plain,
% 5.24/5.45      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 5.24/5.45      inference('sup+', [status(thm)], ['44', '45'])).
% 5.24/5.45  thf('47', plain,
% 5.24/5.45      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 5.24/5.45      inference('sup+', [status(thm)], ['43', '46'])).
% 5.24/5.45  thf('48', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.24/5.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.24/5.45  thf('49', plain,
% 5.24/5.45      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 5.24/5.45      inference('sup+', [status(thm)], ['47', '48'])).
% 5.24/5.45  thf('50', plain,
% 5.24/5.45      (![X16 : $i, X17 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.24/5.45           = (k3_xboole_0 @ X16 @ X17))),
% 5.24/5.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.24/5.45  thf('51', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.24/5.45         (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ 
% 5.24/5.45          (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 5.24/5.45      inference('sup+', [status(thm)], ['38', '41'])).
% 5.24/5.45  thf('52', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ (k3_xboole_0 @ X1 @ X0))),
% 5.24/5.45      inference('sup+', [status(thm)], ['50', '51'])).
% 5.24/5.45  thf('53', plain,
% 5.24/5.45      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0)),
% 5.24/5.45      inference('sup+', [status(thm)], ['49', '52'])).
% 5.24/5.45  thf('54', plain,
% 5.24/5.45      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 5.24/5.45      inference('sup+', [status(thm)], ['47', '48'])).
% 5.24/5.45  thf('55', plain,
% 5.24/5.45      (![X16 : $i, X17 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.24/5.45           = (k3_xboole_0 @ X16 @ X17))),
% 5.24/5.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.24/5.45  thf('56', plain,
% 5.24/5.45      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 5.24/5.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.24/5.45  thf('57', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 5.24/5.45      inference('sup+', [status(thm)], ['55', '56'])).
% 5.24/5.45  thf('58', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 5.24/5.45      inference('sup+', [status(thm)], ['54', '57'])).
% 5.24/5.45  thf(d10_xboole_0, axiom,
% 5.24/5.45    (![A:$i,B:$i]:
% 5.24/5.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.24/5.45  thf('59', plain,
% 5.24/5.45      (![X3 : $i, X5 : $i]:
% 5.24/5.45         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 5.24/5.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.24/5.45  thf('60', plain,
% 5.24/5.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.24/5.45      inference('sup-', [status(thm)], ['58', '59'])).
% 5.24/5.45  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.24/5.45      inference('sup-', [status(thm)], ['53', '60'])).
% 5.24/5.45  thf('62', plain,
% 5.24/5.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 5.24/5.45      inference('sup-', [status(thm)], ['58', '59'])).
% 5.24/5.45  thf('63', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 5.24/5.45      inference('sup-', [status(thm)], ['61', '62'])).
% 5.24/5.45  thf('64', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 5.24/5.45      inference('sup-', [status(thm)], ['42', '63'])).
% 5.24/5.45  thf('65', plain,
% 5.24/5.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 5.24/5.45           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 5.24/5.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.24/5.45  thf('66', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 5.24/5.45      inference('demod', [status(thm)], ['64', '65'])).
% 5.24/5.45  thf('67', plain,
% 5.24/5.45      (![X16 : $i, X17 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.24/5.45           = (k3_xboole_0 @ X16 @ X17))),
% 5.24/5.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.24/5.45  thf('68', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 5.24/5.45           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.24/5.45      inference('sup+', [status(thm)], ['66', '67'])).
% 5.24/5.45  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.24/5.45      inference('sup-', [status(thm)], ['53', '60'])).
% 5.24/5.45  thf('70', plain,
% 5.24/5.45      (![X16 : $i, X17 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.24/5.45           = (k3_xboole_0 @ X16 @ X17))),
% 5.24/5.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.24/5.45  thf('71', plain,
% 5.24/5.45      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 5.24/5.45      inference('sup+', [status(thm)], ['69', '70'])).
% 5.24/5.45  thf('72', plain,
% 5.24/5.45      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 5.24/5.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.24/5.45  thf('73', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 5.24/5.45      inference('simplify', [status(thm)], ['72'])).
% 5.24/5.45  thf('74', plain,
% 5.24/5.45      (![X9 : $i, X10 : $i]:
% 5.24/5.45         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 5.24/5.45      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.24/5.45  thf('75', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 5.24/5.45      inference('sup-', [status(thm)], ['73', '74'])).
% 5.24/5.45  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.24/5.45      inference('demod', [status(thm)], ['71', '75'])).
% 5.24/5.45  thf('77', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.24/5.45      inference('demod', [status(thm)], ['68', '76'])).
% 5.24/5.45  thf('78', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.24/5.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.24/5.45  thf('79', plain,
% 5.24/5.45      (![X16 : $i, X17 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.24/5.45           = (k3_xboole_0 @ X16 @ X17))),
% 5.24/5.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.24/5.45  thf('80', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 5.24/5.45      inference('sup-', [status(thm)], ['34', '35'])).
% 5.24/5.45  thf('81', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 5.24/5.45      inference('sup+', [status(thm)], ['79', '80'])).
% 5.24/5.45  thf('82', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 5.24/5.45      inference('sup+', [status(thm)], ['78', '81'])).
% 5.24/5.45  thf('83', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 5.24/5.45           = (k2_xboole_0 @ X1 @ X0))),
% 5.24/5.45      inference('sup+', [status(thm)], ['77', '82'])).
% 5.24/5.45  thf('84', plain,
% 5.24/5.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 5.24/5.45           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 5.24/5.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.24/5.45  thf('85', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.24/5.45         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 5.24/5.45          (k4_xboole_0 @ X2 @ X1))),
% 5.24/5.45      inference('sup+', [status(thm)], ['39', '40'])).
% 5.24/5.45  thf('86', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.24/5.45         (r1_tarski @ 
% 5.24/5.45          (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 5.24/5.45          (k4_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X1))),
% 5.24/5.45      inference('sup+', [status(thm)], ['84', '85'])).
% 5.24/5.45  thf('87', plain,
% 5.24/5.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 5.24/5.45           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 5.24/5.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.24/5.45  thf('88', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.24/5.45         (r1_tarski @ 
% 5.24/5.45          (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 5.24/5.45          (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ X1)))),
% 5.24/5.45      inference('demod', [status(thm)], ['86', '87'])).
% 5.24/5.45  thf('89', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 5.24/5.45      inference('sup-', [status(thm)], ['61', '62'])).
% 5.24/5.45  thf('90', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 5.24/5.45           (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))) = (k1_xboole_0))),
% 5.24/5.45      inference('sup-', [status(thm)], ['88', '89'])).
% 5.24/5.45  thf('91', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 5.24/5.45           = (k1_xboole_0))),
% 5.24/5.45      inference('sup+', [status(thm)], ['83', '90'])).
% 5.24/5.45  thf('92', plain,
% 5.24/5.45      ((((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_B)
% 5.24/5.45          = (k1_xboole_0)))
% 5.24/5.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.24/5.45      inference('sup+', [status(thm)], ['37', '91'])).
% 5.24/5.45  thf('93', plain,
% 5.24/5.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.24/5.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.45  thf(t65_tops_1, axiom,
% 5.24/5.45    (![A:$i]:
% 5.24/5.45     ( ( l1_pre_topc @ A ) =>
% 5.24/5.45       ( ![B:$i]:
% 5.24/5.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.24/5.45           ( ( k2_pre_topc @ A @ B ) =
% 5.24/5.45             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 5.24/5.45  thf('94', plain,
% 5.24/5.45      (![X28 : $i, X29 : $i]:
% 5.24/5.45         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 5.24/5.45          | ((k2_pre_topc @ X29 @ X28)
% 5.24/5.45              = (k4_subset_1 @ (u1_struct_0 @ X29) @ X28 @ 
% 5.24/5.45                 (k2_tops_1 @ X29 @ X28)))
% 5.24/5.45          | ~ (l1_pre_topc @ X29))),
% 5.24/5.45      inference('cnf', [status(esa)], [t65_tops_1])).
% 5.24/5.45  thf('95', plain,
% 5.24/5.45      ((~ (l1_pre_topc @ sk_A)
% 5.24/5.45        | ((k2_pre_topc @ sk_A @ sk_B)
% 5.24/5.45            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45               (k2_tops_1 @ sk_A @ sk_B))))),
% 5.24/5.45      inference('sup-', [status(thm)], ['93', '94'])).
% 5.24/5.45  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 5.24/5.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.45  thf('97', plain,
% 5.24/5.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.24/5.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.45  thf(dt_k2_tops_1, axiom,
% 5.24/5.45    (![A:$i,B:$i]:
% 5.24/5.45     ( ( ( l1_pre_topc @ A ) & 
% 5.24/5.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.24/5.45       ( m1_subset_1 @
% 5.24/5.45         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.24/5.45  thf('98', plain,
% 5.24/5.45      (![X26 : $i, X27 : $i]:
% 5.24/5.45         (~ (l1_pre_topc @ X26)
% 5.24/5.45          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 5.24/5.45          | (m1_subset_1 @ (k2_tops_1 @ X26 @ X27) @ 
% 5.24/5.45             (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 5.24/5.45      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 5.24/5.45  thf('99', plain,
% 5.24/5.45      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.24/5.45         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.24/5.45        | ~ (l1_pre_topc @ sk_A))),
% 5.24/5.45      inference('sup-', [status(thm)], ['97', '98'])).
% 5.24/5.45  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 5.24/5.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.45  thf('101', plain,
% 5.24/5.45      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.24/5.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.24/5.45      inference('demod', [status(thm)], ['99', '100'])).
% 5.24/5.45  thf('102', plain,
% 5.24/5.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.24/5.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.45  thf(redefinition_k4_subset_1, axiom,
% 5.24/5.45    (![A:$i,B:$i,C:$i]:
% 5.24/5.45     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 5.24/5.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 5.24/5.45       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 5.24/5.45  thf('103', plain,
% 5.24/5.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.24/5.45         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 5.24/5.45          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19))
% 5.24/5.45          | ((k4_subset_1 @ X19 @ X18 @ X20) = (k2_xboole_0 @ X18 @ X20)))),
% 5.24/5.45      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 5.24/5.45  thf('104', plain,
% 5.24/5.45      (![X0 : $i]:
% 5.24/5.45         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 5.24/5.45            = (k2_xboole_0 @ sk_B @ X0))
% 5.24/5.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.24/5.45      inference('sup-', [status(thm)], ['102', '103'])).
% 5.24/5.45  thf('105', plain,
% 5.24/5.45      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 5.24/5.45         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.24/5.45      inference('sup-', [status(thm)], ['101', '104'])).
% 5.24/5.45  thf('106', plain,
% 5.24/5.45      (((k2_pre_topc @ sk_A @ sk_B)
% 5.24/5.45         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.24/5.45      inference('demod', [status(thm)], ['95', '96', '105'])).
% 5.24/5.45  thf('107', plain,
% 5.24/5.45      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 5.24/5.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.24/5.45      inference('demod', [status(thm)], ['92', '106'])).
% 5.24/5.45  thf('108', plain,
% 5.24/5.45      (![X16 : $i, X17 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.24/5.45           = (k3_xboole_0 @ X16 @ X17))),
% 5.24/5.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.24/5.45  thf('109', plain,
% 5.24/5.45      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ k1_xboole_0)
% 5.24/5.45          = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 5.24/5.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.24/5.45      inference('sup+', [status(thm)], ['107', '108'])).
% 5.24/5.45  thf('110', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.24/5.45      inference('demod', [status(thm)], ['71', '75'])).
% 5.24/5.45  thf('111', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.24/5.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.24/5.45  thf('112', plain,
% 5.24/5.45      (((k2_pre_topc @ sk_A @ sk_B)
% 5.24/5.45         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.24/5.45      inference('demod', [status(thm)], ['95', '96', '105'])).
% 5.24/5.45  thf('113', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 5.24/5.45      inference('sup-', [status(thm)], ['53', '60'])).
% 5.24/5.45  thf('114', plain,
% 5.24/5.45      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 5.24/5.45      inference('sup+', [status(thm)], ['44', '45'])).
% 5.24/5.45  thf('115', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 5.24/5.45      inference('sup+', [status(thm)], ['113', '114'])).
% 5.24/5.45  thf('116', plain,
% 5.24/5.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 5.24/5.45           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 5.24/5.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 5.24/5.45  thf('117', plain,
% 5.24/5.45      (![X0 : $i, X1 : $i]:
% 5.24/5.45         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 5.24/5.45      inference('demod', [status(thm)], ['115', '116'])).
% 5.24/5.45  thf('118', plain,
% 5.24/5.45      (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 5.24/5.45      inference('sup+', [status(thm)], ['112', '117'])).
% 5.24/5.45  thf('119', plain,
% 5.24/5.45      (![X16 : $i, X17 : $i]:
% 5.24/5.45         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.24/5.45           = (k3_xboole_0 @ X16 @ X17))),
% 5.24/5.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.24/5.45  thf('120', plain,
% 5.24/5.45      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 5.24/5.45         = (k3_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 5.24/5.45      inference('sup+', [status(thm)], ['118', '119'])).
% 5.24/5.45  thf('121', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 5.24/5.45      inference('demod', [status(thm)], ['71', '75'])).
% 5.24/5.45  thf('122', plain,
% 5.24/5.45      (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 5.24/5.45      inference('demod', [status(thm)], ['120', '121'])).
% 5.24/5.45  thf('123', plain,
% 5.24/5.45      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 5.24/5.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.24/5.45      inference('demod', [status(thm)], ['109', '110', '111', '122'])).
% 5.24/5.45  thf('124', plain,
% 5.24/5.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.24/5.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.45  thf(t52_pre_topc, axiom,
% 5.24/5.45    (![A:$i]:
% 5.24/5.45     ( ( l1_pre_topc @ A ) =>
% 5.24/5.45       ( ![B:$i]:
% 5.24/5.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.24/5.45           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 5.24/5.45             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 5.24/5.45               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 5.24/5.46  thf('125', plain,
% 5.24/5.46      (![X24 : $i, X25 : $i]:
% 5.24/5.46         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 5.24/5.46          | ~ (v2_pre_topc @ X25)
% 5.24/5.46          | ((k2_pre_topc @ X25 @ X24) != (X24))
% 5.24/5.46          | (v4_pre_topc @ X24 @ X25)
% 5.24/5.46          | ~ (l1_pre_topc @ X25))),
% 5.24/5.46      inference('cnf', [status(esa)], [t52_pre_topc])).
% 5.24/5.46  thf('126', plain,
% 5.24/5.46      ((~ (l1_pre_topc @ sk_A)
% 5.24/5.46        | (v4_pre_topc @ sk_B @ sk_A)
% 5.24/5.46        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 5.24/5.46        | ~ (v2_pre_topc @ sk_A))),
% 5.24/5.46      inference('sup-', [status(thm)], ['124', '125'])).
% 5.24/5.46  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 5.24/5.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.46  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 5.24/5.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.24/5.46  thf('129', plain,
% 5.24/5.46      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 5.24/5.46      inference('demod', [status(thm)], ['126', '127', '128'])).
% 5.24/5.46  thf('130', plain,
% 5.24/5.46      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 5.24/5.46         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.46                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.46                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.24/5.46      inference('sup-', [status(thm)], ['123', '129'])).
% 5.24/5.46  thf('131', plain,
% 5.24/5.46      (((v4_pre_topc @ sk_B @ sk_A))
% 5.24/5.46         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.46                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.46                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.24/5.46      inference('simplify', [status(thm)], ['130'])).
% 5.24/5.46  thf('132', plain,
% 5.24/5.46      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 5.24/5.46      inference('split', [status(esa)], ['0'])).
% 5.24/5.46  thf('133', plain,
% 5.24/5.46      (~
% 5.24/5.46       (((k2_tops_1 @ sk_A @ sk_B)
% 5.24/5.46          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.24/5.46             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 5.24/5.46       ((v4_pre_topc @ sk_B @ sk_A))),
% 5.24/5.46      inference('sup-', [status(thm)], ['131', '132'])).
% 5.24/5.46  thf('134', plain, ($false),
% 5.24/5.46      inference('sat_resolution*', [status(thm)], ['1', '29', '30', '133'])).
% 5.24/5.46  
% 5.24/5.46  % SZS output end Refutation
% 5.24/5.46  
% 5.30/5.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
