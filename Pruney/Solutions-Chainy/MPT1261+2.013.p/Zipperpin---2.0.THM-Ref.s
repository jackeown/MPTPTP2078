%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kfhrr8K69G

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:38 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 484 expanded)
%              Number of leaves         :   43 ( 159 expanded)
%              Depth                    :   18
%              Number of atoms          : 1377 (5566 expanded)
%              Number of equality atoms :  111 ( 384 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k2_tops_1 @ X42 @ X41 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k2_pre_topc @ X42 @ X41 ) @ ( k1_tops_1 @ X42 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v4_pre_topc @ X37 @ X38 )
      | ( ( k2_pre_topc @ X38 @ X37 )
        = X37 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k7_subset_1 @ X30 @ X29 @ X31 )
        = ( k4_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('19',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('21',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('29',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X25 @ ( k3_subset_1 @ X25 @ X24 ) )
        = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','48'])).

thf('50',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','49'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('52',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('53',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X19 @ X18 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('72',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('76',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['67','76'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('78',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('79',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('82',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) )
      | ( ( k4_subset_1 @ X27 @ X26 @ X28 )
        = ( k2_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('87',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( ( k2_pre_topc @ X44 @ X43 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X44 ) @ X43 @ ( k2_tops_1 @ X44 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['67','76'])).

thf('92',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['85','90','91'])).

thf('93',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['66','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('95',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X39 @ X40 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('96',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['93','99'])).

thf('101',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('102',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('104',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','102','103'])).

thf('105',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['12','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('107',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','105','106'])).

thf('108',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('110',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['14','102'])).

thf('112',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['110','111'])).

thf('113',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['107','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kfhrr8K69G
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.68  % Solved by: fo/fo7.sh
% 0.44/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.68  % done 931 iterations in 0.261s
% 0.44/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.68  % SZS output start Refutation
% 0.44/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.68  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.44/0.68  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.44/0.68  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.44/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.68  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.44/0.68  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.44/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.44/0.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.44/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.68  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.44/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.68  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.44/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.68  thf(t77_tops_1, conjecture,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.68       ( ![B:$i]:
% 0.44/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.68           ( ( v4_pre_topc @ B @ A ) <=>
% 0.44/0.68             ( ( k2_tops_1 @ A @ B ) =
% 0.44/0.68               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.44/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.68    (~( ![A:$i]:
% 0.44/0.68        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.68          ( ![B:$i]:
% 0.44/0.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.68              ( ( v4_pre_topc @ B @ A ) <=>
% 0.44/0.68                ( ( k2_tops_1 @ A @ B ) =
% 0.44/0.68                  ( k7_subset_1 @
% 0.44/0.68                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.44/0.68    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.44/0.68  thf('0', plain,
% 0.44/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(l78_tops_1, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( l1_pre_topc @ A ) =>
% 0.44/0.68       ( ![B:$i]:
% 0.44/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.68           ( ( k2_tops_1 @ A @ B ) =
% 0.44/0.68             ( k7_subset_1 @
% 0.44/0.68               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.44/0.68               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.44/0.68  thf('1', plain,
% 0.44/0.68      (![X41 : $i, X42 : $i]:
% 0.44/0.68         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.44/0.68          | ((k2_tops_1 @ X42 @ X41)
% 0.44/0.68              = (k7_subset_1 @ (u1_struct_0 @ X42) @ 
% 0.44/0.68                 (k2_pre_topc @ X42 @ X41) @ (k1_tops_1 @ X42 @ X41)))
% 0.44/0.68          | ~ (l1_pre_topc @ X42))),
% 0.44/0.68      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.44/0.68  thf('2', plain,
% 0.44/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.68        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.68            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.68               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.44/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.68  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('4', plain,
% 0.44/0.68      (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.68         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.44/0.68            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.44/0.68      inference('demod', [status(thm)], ['2', '3'])).
% 0.44/0.68  thf('5', plain,
% 0.44/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.68             (k1_tops_1 @ sk_A @ sk_B)))
% 0.44/0.68        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('6', plain,
% 0.44/0.68      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.68      inference('split', [status(esa)], ['5'])).
% 0.44/0.68  thf('7', plain,
% 0.44/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(t52_pre_topc, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( l1_pre_topc @ A ) =>
% 0.44/0.68       ( ![B:$i]:
% 0.44/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.68           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.44/0.68             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.44/0.68               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.44/0.68  thf('8', plain,
% 0.44/0.68      (![X37 : $i, X38 : $i]:
% 0.44/0.68         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.44/0.68          | ~ (v4_pre_topc @ X37 @ X38)
% 0.44/0.68          | ((k2_pre_topc @ X38 @ X37) = (X37))
% 0.44/0.68          | ~ (l1_pre_topc @ X38))),
% 0.44/0.68      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.44/0.68  thf('9', plain,
% 0.44/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.68        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.44/0.68        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.68  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('11', plain,
% 0.44/0.68      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.68      inference('demod', [status(thm)], ['9', '10'])).
% 0.44/0.68  thf('12', plain,
% 0.44/0.68      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.44/0.68         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.68      inference('sup-', [status(thm)], ['6', '11'])).
% 0.44/0.68  thf('13', plain,
% 0.44/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.68          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.68              (k1_tops_1 @ sk_A @ sk_B)))
% 0.44/0.68        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('14', plain,
% 0.44/0.68      (~
% 0.44/0.68       (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.68             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.44/0.68       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.68      inference('split', [status(esa)], ['13'])).
% 0.44/0.68  thf('15', plain,
% 0.44/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(redefinition_k7_subset_1, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i]:
% 0.44/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.68       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.44/0.68  thf('16', plain,
% 0.44/0.68      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.44/0.68         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.44/0.68          | ((k7_subset_1 @ X30 @ X29 @ X31) = (k4_xboole_0 @ X29 @ X31)))),
% 0.44/0.68      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.44/0.68  thf('17', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.44/0.68           = (k4_xboole_0 @ sk_B @ X0))),
% 0.44/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.68  thf('18', plain,
% 0.44/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.68          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.68             (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.68      inference('split', [status(esa)], ['5'])).
% 0.44/0.68  thf('19', plain,
% 0.44/0.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.68          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.68         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.68                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.68                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('sup+', [status(thm)], ['17', '18'])).
% 0.44/0.69  thf(t36_xboole_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.44/0.69  thf('20', plain,
% 0.44/0.69      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.44/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.69  thf('21', plain,
% 0.44/0.69      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('sup+', [status(thm)], ['19', '20'])).
% 0.44/0.69  thf(t28_xboole_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.69  thf('22', plain,
% 0.44/0.69      (![X10 : $i, X11 : $i]:
% 0.44/0.69         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.44/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.69  thf('23', plain,
% 0.44/0.69      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.44/0.69          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.44/0.69  thf(t100_xboole_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.69  thf('24', plain,
% 0.44/0.69      (![X3 : $i, X4 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X3 @ X4)
% 0.44/0.69           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.44/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.69  thf('25', plain,
% 0.44/0.69      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.44/0.69          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.44/0.69             (k2_tops_1 @ sk_A @ sk_B))))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('sup+', [status(thm)], ['23', '24'])).
% 0.44/0.69  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.69  thf('26', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.44/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.69  thf(t3_subset, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.69  thf('27', plain,
% 0.44/0.69      (![X34 : $i, X36 : $i]:
% 0.44/0.69         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 0.44/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.69  thf('28', plain,
% 0.44/0.69      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.69  thf(involutiveness_k3_subset_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.69       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.44/0.69  thf('29', plain,
% 0.44/0.69      (![X24 : $i, X25 : $i]:
% 0.44/0.69         (((k3_subset_1 @ X25 @ (k3_subset_1 @ X25 @ X24)) = (X24))
% 0.44/0.69          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.44/0.69      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.44/0.69  thf('30', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['28', '29'])).
% 0.44/0.69  thf('31', plain,
% 0.44/0.69      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.69  thf(d5_subset_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.69       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.44/0.69  thf('32', plain,
% 0.44/0.69      (![X22 : $i, X23 : $i]:
% 0.44/0.69         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.44/0.69          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.44/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.44/0.69  thf('33', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.69  thf(t3_boole, axiom,
% 0.44/0.69    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.69  thf('34', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.44/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.69  thf('35', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['33', '34'])).
% 0.44/0.69  thf('36', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.69      inference('demod', [status(thm)], ['30', '35'])).
% 0.44/0.69  thf(d10_xboole_0, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.69  thf('37', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.44/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.69  thf('38', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.44/0.69      inference('simplify', [status(thm)], ['37'])).
% 0.44/0.69  thf('39', plain,
% 0.44/0.69      (![X34 : $i, X36 : $i]:
% 0.44/0.69         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 0.44/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.69  thf('40', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['38', '39'])).
% 0.44/0.69  thf('41', plain,
% 0.44/0.69      (![X22 : $i, X23 : $i]:
% 0.44/0.69         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.44/0.69          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.44/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.44/0.69  thf('42', plain,
% 0.44/0.69      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['40', '41'])).
% 0.44/0.69  thf('43', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.44/0.69      inference('simplify', [status(thm)], ['37'])).
% 0.44/0.69  thf('44', plain,
% 0.44/0.69      (![X10 : $i, X11 : $i]:
% 0.44/0.69         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.44/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.69  thf('45', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['43', '44'])).
% 0.44/0.69  thf('46', plain,
% 0.44/0.69      (![X3 : $i, X4 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X3 @ X4)
% 0.44/0.69           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.44/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.69  thf('47', plain,
% 0.44/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['45', '46'])).
% 0.44/0.69  thf('48', plain,
% 0.44/0.69      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['42', '47'])).
% 0.44/0.69  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.69      inference('demod', [status(thm)], ['36', '48'])).
% 0.44/0.69  thf('50', plain,
% 0.44/0.69      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('demod', [status(thm)], ['25', '49'])).
% 0.44/0.69  thf(t98_xboole_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.44/0.69  thf('51', plain,
% 0.44/0.69      (![X16 : $i, X17 : $i]:
% 0.44/0.69         ((k2_xboole_0 @ X16 @ X17)
% 0.44/0.69           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.44/0.69      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.44/0.69  thf('52', plain,
% 0.44/0.69      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.44/0.69          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('sup+', [status(thm)], ['50', '51'])).
% 0.44/0.69  thf(commutativity_k2_tarski, axiom,
% 0.44/0.69    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.44/0.69  thf('53', plain,
% 0.44/0.69      (![X18 : $i, X19 : $i]:
% 0.44/0.69         ((k2_tarski @ X19 @ X18) = (k2_tarski @ X18 @ X19))),
% 0.44/0.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.44/0.69  thf(t12_setfam_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.69  thf('54', plain,
% 0.44/0.69      (![X32 : $i, X33 : $i]:
% 0.44/0.69         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.44/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.44/0.69  thf('55', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]:
% 0.44/0.69         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.69      inference('sup+', [status(thm)], ['53', '54'])).
% 0.44/0.69  thf('56', plain,
% 0.44/0.69      (![X32 : $i, X33 : $i]:
% 0.44/0.69         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.44/0.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.44/0.69  thf('57', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.69      inference('sup+', [status(thm)], ['55', '56'])).
% 0.44/0.69  thf('58', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.44/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.69  thf('59', plain,
% 0.44/0.69      (![X10 : $i, X11 : $i]:
% 0.44/0.69         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.44/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.69  thf('60', plain,
% 0.44/0.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['58', '59'])).
% 0.44/0.69  thf('61', plain,
% 0.44/0.69      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['57', '60'])).
% 0.44/0.69  thf('62', plain,
% 0.44/0.69      (![X3 : $i, X4 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X3 @ X4)
% 0.44/0.69           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.44/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.69  thf('63', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['61', '62'])).
% 0.44/0.69  thf('64', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.44/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.69  thf('65', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.69      inference('sup+', [status(thm)], ['63', '64'])).
% 0.44/0.69  thf('66', plain,
% 0.44/0.69      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('demod', [status(thm)], ['52', '65'])).
% 0.44/0.69  thf('67', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.69      inference('sup+', [status(thm)], ['55', '56'])).
% 0.44/0.69  thf('68', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('69', plain,
% 0.44/0.69      (![X34 : $i, X35 : $i]:
% 0.44/0.69         ((r1_tarski @ X34 @ X35) | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.44/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.69  thf('70', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.69      inference('sup-', [status(thm)], ['68', '69'])).
% 0.44/0.69  thf('71', plain,
% 0.44/0.69      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('sup+', [status(thm)], ['19', '20'])).
% 0.44/0.69  thf(t1_xboole_1, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.44/0.69       ( r1_tarski @ A @ C ) ))).
% 0.44/0.69  thf('72', plain,
% 0.44/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.69         (~ (r1_tarski @ X7 @ X8)
% 0.44/0.69          | ~ (r1_tarski @ X8 @ X9)
% 0.44/0.69          | (r1_tarski @ X7 @ X9))),
% 0.44/0.69      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.44/0.69  thf('73', plain,
% 0.44/0.69      ((![X0 : $i]:
% 0.44/0.69          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.44/0.69           | ~ (r1_tarski @ sk_B @ X0)))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['71', '72'])).
% 0.44/0.69  thf('74', plain,
% 0.44/0.69      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['70', '73'])).
% 0.44/0.69  thf('75', plain,
% 0.44/0.69      (![X10 : $i, X11 : $i]:
% 0.44/0.69         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.44/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.69  thf('76', plain,
% 0.44/0.69      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.44/0.69          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['74', '75'])).
% 0.44/0.69  thf('77', plain,
% 0.44/0.69      ((((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.44/0.69          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('sup+', [status(thm)], ['67', '76'])).
% 0.44/0.69  thf(t17_xboole_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.44/0.69  thf('78', plain,
% 0.44/0.69      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.44/0.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.44/0.69  thf('79', plain,
% 0.44/0.69      (![X34 : $i, X36 : $i]:
% 0.44/0.69         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 0.44/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.69  thf('80', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i]:
% 0.44/0.69         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['78', '79'])).
% 0.44/0.69  thf('81', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(redefinition_k4_subset_1, axiom,
% 0.44/0.69    (![A:$i,B:$i,C:$i]:
% 0.44/0.69     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.44/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.44/0.69       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.44/0.69  thf('82', plain,
% 0.44/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.44/0.69          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27))
% 0.44/0.69          | ((k4_subset_1 @ X27 @ X26 @ X28) = (k2_xboole_0 @ X26 @ X28)))),
% 0.44/0.69      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.44/0.69  thf('83', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.44/0.69            = (k2_xboole_0 @ sk_B @ X0))
% 0.44/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['81', '82'])).
% 0.44/0.69  thf('84', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69           (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.44/0.69           = (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['80', '83'])).
% 0.44/0.69  thf('85', plain,
% 0.44/0.69      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.44/0.69          = (k2_xboole_0 @ sk_B @ 
% 0.44/0.69             (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('sup+', [status(thm)], ['77', '84'])).
% 0.44/0.69  thf('86', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(t65_tops_1, axiom,
% 0.44/0.69    (![A:$i]:
% 0.44/0.69     ( ( l1_pre_topc @ A ) =>
% 0.44/0.69       ( ![B:$i]:
% 0.44/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.69           ( ( k2_pre_topc @ A @ B ) =
% 0.44/0.69             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.44/0.69  thf('87', plain,
% 0.44/0.69      (![X43 : $i, X44 : $i]:
% 0.44/0.69         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.44/0.69          | ((k2_pre_topc @ X44 @ X43)
% 0.44/0.69              = (k4_subset_1 @ (u1_struct_0 @ X44) @ X43 @ 
% 0.44/0.69                 (k2_tops_1 @ X44 @ X43)))
% 0.44/0.69          | ~ (l1_pre_topc @ X44))),
% 0.44/0.69      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.44/0.69  thf('88', plain,
% 0.44/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.69        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.44/0.69            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['86', '87'])).
% 0.44/0.69  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('90', plain,
% 0.44/0.69      (((k2_pre_topc @ sk_A @ sk_B)
% 0.44/0.69         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.44/0.69      inference('demod', [status(thm)], ['88', '89'])).
% 0.44/0.69  thf('91', plain,
% 0.44/0.69      ((((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.44/0.69          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('sup+', [status(thm)], ['67', '76'])).
% 0.44/0.69  thf('92', plain,
% 0.44/0.69      ((((k2_pre_topc @ sk_A @ sk_B)
% 0.44/0.69          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('demod', [status(thm)], ['85', '90', '91'])).
% 0.44/0.69  thf('93', plain,
% 0.44/0.69      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('sup+', [status(thm)], ['66', '92'])).
% 0.44/0.69  thf('94', plain,
% 0.44/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf(fc1_tops_1, axiom,
% 0.44/0.69    (![A:$i,B:$i]:
% 0.44/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.44/0.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.44/0.69       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.44/0.69  thf('95', plain,
% 0.44/0.69      (![X39 : $i, X40 : $i]:
% 0.44/0.69         (~ (l1_pre_topc @ X39)
% 0.44/0.69          | ~ (v2_pre_topc @ X39)
% 0.44/0.69          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.44/0.69          | (v4_pre_topc @ (k2_pre_topc @ X39 @ X40) @ X39))),
% 0.44/0.69      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.44/0.69  thf('96', plain,
% 0.44/0.69      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.44/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.44/0.69        | ~ (l1_pre_topc @ sk_A))),
% 0.44/0.69      inference('sup-', [status(thm)], ['94', '95'])).
% 0.44/0.69  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('99', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.44/0.69      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.44/0.69  thf('100', plain,
% 0.44/0.69      (((v4_pre_topc @ sk_B @ sk_A))
% 0.44/0.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('sup+', [status(thm)], ['93', '99'])).
% 0.44/0.69  thf('101', plain,
% 0.44/0.69      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.44/0.69      inference('split', [status(esa)], ['13'])).
% 0.44/0.69  thf('102', plain,
% 0.44/0.69      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.44/0.69       ~
% 0.44/0.69       (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.44/0.69      inference('sup-', [status(thm)], ['100', '101'])).
% 0.44/0.69  thf('103', plain,
% 0.44/0.69      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.44/0.69       (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.44/0.69      inference('split', [status(esa)], ['5'])).
% 0.44/0.69  thf('104', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.44/0.69      inference('sat_resolution*', [status(thm)], ['14', '102', '103'])).
% 0.44/0.69  thf('105', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.44/0.69      inference('simpl_trail', [status(thm)], ['12', '104'])).
% 0.44/0.69  thf('106', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.44/0.69           = (k4_xboole_0 @ sk_B @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.69  thf('107', plain,
% 0.44/0.69      (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.44/0.69      inference('demod', [status(thm)], ['4', '105', '106'])).
% 0.44/0.69  thf('108', plain,
% 0.44/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69              (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.69         <= (~
% 0.44/0.69             (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('split', [status(esa)], ['13'])).
% 0.44/0.69  thf('109', plain,
% 0.44/0.69      (![X0 : $i]:
% 0.44/0.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.44/0.69           = (k4_xboole_0 @ sk_B @ X0))),
% 0.44/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.69  thf('110', plain,
% 0.44/0.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.69         <= (~
% 0.44/0.69             (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.44/0.69      inference('demod', [status(thm)], ['108', '109'])).
% 0.44/0.69  thf('111', plain,
% 0.44/0.69      (~
% 0.44/0.69       (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.69             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.44/0.69      inference('sat_resolution*', [status(thm)], ['14', '102'])).
% 0.44/0.69  thf('112', plain,
% 0.44/0.69      (((k2_tops_1 @ sk_A @ sk_B)
% 0.44/0.69         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.44/0.69      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 0.44/0.69  thf('113', plain, ($false),
% 0.44/0.69      inference('simplify_reflect-', [status(thm)], ['107', '112'])).
% 0.44/0.69  
% 0.44/0.69  % SZS output end Refutation
% 0.44/0.69  
% 0.51/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
