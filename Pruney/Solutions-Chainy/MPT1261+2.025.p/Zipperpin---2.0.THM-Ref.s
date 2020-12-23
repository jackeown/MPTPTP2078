%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C2zzGLb8ys

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:40 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 458 expanded)
%              Number of leaves         :   39 ( 150 expanded)
%              Depth                    :   16
%              Number of atoms          : 1465 (5931 expanded)
%              Number of equality atoms :  108 ( 391 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( ( k1_tops_1 @ X57 @ X56 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X57 ) @ X56 @ ( k2_tops_1 @ X57 @ X56 ) ) )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k7_subset_1 @ X37 @ X36 @ X38 )
        = ( k4_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k7_subset_1 @ X37 @ X36 @ X38 )
        = ( k6_subset_1 @ X36 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('13',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k6_subset_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('21',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X55 @ X54 ) @ X54 )
      | ~ ( v4_pre_topc @ X54 @ X55 )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X43: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('28',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X27 @ ( k3_subset_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('29',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k6_subset_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('32',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf('34',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['17','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('43',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('45',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['18'])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X24: $i,X25: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k4_subset_1 @ X32 @ X31 @ X33 )
        = ( k2_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
          = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k4_subset_1 @ X39 @ X40 @ ( k3_subset_1 @ X39 @ X40 ) )
        = ( k2_subset_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('61',plain,(
    ! [X19: $i] :
      ( ( k2_subset_1 @ X19 )
      = X19 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('62',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k4_subset_1 @ X39 @ X40 @ ( k3_subset_1 @ X39 @ X40 ) )
        = X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('65',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k6_subset_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('66',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','67'])).

thf('69',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['57','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('71',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

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
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( ( k2_pre_topc @ X53 @ X52 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X53 ) @ X52 @ ( k2_tops_1 @ X53 @ X52 ) ) )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('80',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( l1_pre_topc @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X48 @ X49 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('81',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k4_subset_1 @ X32 @ X31 @ X33 )
        = ( k2_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('90',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74','88','89'])).

thf('91',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['57','68'])).

thf('92',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
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

thf('94',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( v2_pre_topc @ X47 )
      | ( ( k2_pre_topc @ X47 @ X46 )
       != X46 )
      | ( v4_pre_topc @ X46 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('102',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','41','42','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C2zzGLb8ys
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:03:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.06/1.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.24  % Solved by: fo/fo7.sh
% 1.06/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.24  % done 1636 iterations in 0.801s
% 1.06/1.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.24  % SZS output start Refutation
% 1.06/1.24  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.06/1.24  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.06/1.24  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.06/1.24  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.06/1.24  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.06/1.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.24  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.24  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.24  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.24  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.06/1.24  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.06/1.24  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.06/1.24  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.06/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.24  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.06/1.24  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.06/1.24  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.24  thf(t77_tops_1, conjecture,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.24       ( ![B:$i]:
% 1.06/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.24           ( ( v4_pre_topc @ B @ A ) <=>
% 1.06/1.24             ( ( k2_tops_1 @ A @ B ) =
% 1.06/1.24               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.06/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.24    (~( ![A:$i]:
% 1.06/1.24        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.24          ( ![B:$i]:
% 1.06/1.24            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.24              ( ( v4_pre_topc @ B @ A ) <=>
% 1.06/1.24                ( ( k2_tops_1 @ A @ B ) =
% 1.06/1.24                  ( k7_subset_1 @
% 1.06/1.24                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.06/1.24    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.06/1.24  thf('0', plain,
% 1.06/1.24      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24              (k1_tops_1 @ sk_A @ sk_B)))
% 1.06/1.24        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('1', plain,
% 1.06/1.24      (~
% 1.06/1.24       (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.06/1.24       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.24      inference('split', [status(esa)], ['0'])).
% 1.06/1.24  thf('2', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(t74_tops_1, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( l1_pre_topc @ A ) =>
% 1.06/1.24       ( ![B:$i]:
% 1.06/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.24           ( ( k1_tops_1 @ A @ B ) =
% 1.06/1.24             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.06/1.24  thf('3', plain,
% 1.06/1.24      (![X56 : $i, X57 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 1.06/1.24          | ((k1_tops_1 @ X57 @ X56)
% 1.06/1.24              = (k7_subset_1 @ (u1_struct_0 @ X57) @ X56 @ 
% 1.06/1.24                 (k2_tops_1 @ X57 @ X56)))
% 1.06/1.24          | ~ (l1_pre_topc @ X57))),
% 1.06/1.24      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.06/1.24  thf('4', plain,
% 1.06/1.24      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.24        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.24            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.06/1.24      inference('sup-', [status(thm)], ['2', '3'])).
% 1.06/1.24  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('6', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(redefinition_k7_subset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i]:
% 1.06/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.24       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.06/1.24  thf('7', plain,
% 1.06/1.24      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 1.06/1.24          | ((k7_subset_1 @ X37 @ X36 @ X38) = (k4_xboole_0 @ X36 @ X38)))),
% 1.06/1.24      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.06/1.24  thf(redefinition_k6_subset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.06/1.24  thf('8', plain,
% 1.06/1.24      (![X34 : $i, X35 : $i]:
% 1.06/1.24         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 1.06/1.24      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.24  thf('9', plain,
% 1.06/1.24      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 1.06/1.24          | ((k7_subset_1 @ X37 @ X36 @ X38) = (k6_subset_1 @ X36 @ X38)))),
% 1.06/1.24      inference('demod', [status(thm)], ['7', '8'])).
% 1.06/1.24  thf('10', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.24           = (k6_subset_1 @ sk_B @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['6', '9'])).
% 1.06/1.24  thf('11', plain,
% 1.06/1.24      (((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.24         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.24      inference('demod', [status(thm)], ['4', '5', '10'])).
% 1.06/1.24  thf(dt_k6_subset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.06/1.24  thf('12', plain,
% 1.06/1.24      (![X24 : $i, X25 : $i]:
% 1.06/1.24         (m1_subset_1 @ (k6_subset_1 @ X24 @ X25) @ (k1_zfmisc_1 @ X24))),
% 1.06/1.24      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.06/1.24  thf('13', plain,
% 1.06/1.24      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 1.06/1.24      inference('sup+', [status(thm)], ['11', '12'])).
% 1.06/1.24  thf(d5_subset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.24       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.06/1.24  thf('14', plain,
% 1.06/1.24      (![X20 : $i, X21 : $i]:
% 1.06/1.24         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 1.06/1.24          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 1.06/1.24      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.06/1.24  thf('15', plain,
% 1.06/1.24      (![X34 : $i, X35 : $i]:
% 1.06/1.24         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 1.06/1.24      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.24  thf('16', plain,
% 1.06/1.24      (![X20 : $i, X21 : $i]:
% 1.06/1.24         (((k3_subset_1 @ X20 @ X21) = (k6_subset_1 @ X20 @ X21))
% 1.06/1.24          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 1.06/1.24      inference('demod', [status(thm)], ['14', '15'])).
% 1.06/1.24  thf('17', plain,
% 1.06/1.24      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.06/1.24         = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['13', '16'])).
% 1.06/1.24  thf('18', plain,
% 1.06/1.24      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24             (k1_tops_1 @ sk_A @ sk_B)))
% 1.06/1.24        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('19', plain,
% 1.06/1.24      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.24      inference('split', [status(esa)], ['18'])).
% 1.06/1.24  thf('20', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(t69_tops_1, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( l1_pre_topc @ A ) =>
% 1.06/1.24       ( ![B:$i]:
% 1.06/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.24           ( ( v4_pre_topc @ B @ A ) =>
% 1.06/1.24             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.06/1.24  thf('21', plain,
% 1.06/1.24      (![X54 : $i, X55 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 1.06/1.24          | (r1_tarski @ (k2_tops_1 @ X55 @ X54) @ X54)
% 1.06/1.24          | ~ (v4_pre_topc @ X54 @ X55)
% 1.06/1.24          | ~ (l1_pre_topc @ X55))),
% 1.06/1.24      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.06/1.24  thf('22', plain,
% 1.06/1.24      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.24        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.06/1.24        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.06/1.24      inference('sup-', [status(thm)], ['20', '21'])).
% 1.06/1.24  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('24', plain,
% 1.06/1.24      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.06/1.24        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['22', '23'])).
% 1.06/1.24  thf('25', plain,
% 1.06/1.24      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.06/1.24         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['19', '24'])).
% 1.06/1.24  thf(t3_subset, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.24  thf('26', plain,
% 1.06/1.24      (![X43 : $i, X45 : $i]:
% 1.06/1.24         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X45)) | ~ (r1_tarski @ X43 @ X45))),
% 1.06/1.24      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.24  thf('27', plain,
% 1.06/1.24      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.06/1.24         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['25', '26'])).
% 1.06/1.24  thf(involutiveness_k3_subset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.24       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.06/1.24  thf('28', plain,
% 1.06/1.24      (![X26 : $i, X27 : $i]:
% 1.06/1.24         (((k3_subset_1 @ X27 @ (k3_subset_1 @ X27 @ X26)) = (X26))
% 1.06/1.24          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 1.06/1.24      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.06/1.24  thf('29', plain,
% 1.06/1.24      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.24          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.24         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['27', '28'])).
% 1.06/1.24  thf('30', plain,
% 1.06/1.24      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.06/1.24         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['25', '26'])).
% 1.06/1.24  thf('31', plain,
% 1.06/1.24      (![X20 : $i, X21 : $i]:
% 1.06/1.24         (((k3_subset_1 @ X20 @ X21) = (k6_subset_1 @ X20 @ X21))
% 1.06/1.24          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 1.06/1.24      inference('demod', [status(thm)], ['14', '15'])).
% 1.06/1.24  thf('32', plain,
% 1.06/1.24      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.24          = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.06/1.24         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['30', '31'])).
% 1.06/1.24  thf('33', plain,
% 1.06/1.24      (((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.24         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.24      inference('demod', [status(thm)], ['4', '5', '10'])).
% 1.06/1.24  thf('34', plain,
% 1.06/1.24      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.24          = (k1_tops_1 @ sk_A @ sk_B)))
% 1.06/1.24         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.24      inference('demod', [status(thm)], ['32', '33'])).
% 1.06/1.24  thf('35', plain,
% 1.06/1.24      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.06/1.24          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.24         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.24      inference('demod', [status(thm)], ['29', '34'])).
% 1.06/1.24  thf('36', plain,
% 1.06/1.24      ((((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.06/1.24          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.24         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.24      inference('sup+', [status(thm)], ['17', '35'])).
% 1.06/1.24  thf('37', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.24           = (k6_subset_1 @ sk_B @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['6', '9'])).
% 1.06/1.24  thf('38', plain,
% 1.06/1.24      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24              (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.24         <= (~
% 1.06/1.24             (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('split', [status(esa)], ['0'])).
% 1.06/1.24  thf('39', plain,
% 1.06/1.24      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.24         <= (~
% 1.06/1.24             (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup-', [status(thm)], ['37', '38'])).
% 1.06/1.24  thf('40', plain,
% 1.06/1.24      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.24         <= (~
% 1.06/1.24             (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.06/1.24             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['36', '39'])).
% 1.06/1.24  thf('41', plain,
% 1.06/1.24      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.06/1.24       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.24      inference('simplify', [status(thm)], ['40'])).
% 1.06/1.24  thf('42', plain,
% 1.06/1.24      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.06/1.24       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.24      inference('split', [status(esa)], ['18'])).
% 1.06/1.24  thf('43', plain,
% 1.06/1.24      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 1.06/1.24      inference('sup+', [status(thm)], ['11', '12'])).
% 1.06/1.24  thf('44', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.24           = (k6_subset_1 @ sk_B @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['6', '9'])).
% 1.06/1.24  thf('45', plain,
% 1.06/1.24      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24             (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('split', [status(esa)], ['18'])).
% 1.06/1.24  thf('46', plain,
% 1.06/1.24      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup+', [status(thm)], ['44', '45'])).
% 1.06/1.24  thf('47', plain,
% 1.06/1.24      (![X24 : $i, X25 : $i]:
% 1.06/1.24         (m1_subset_1 @ (k6_subset_1 @ X24 @ X25) @ (k1_zfmisc_1 @ X24))),
% 1.06/1.24      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.06/1.24  thf('48', plain,
% 1.06/1.24      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup+', [status(thm)], ['46', '47'])).
% 1.06/1.24  thf(redefinition_k4_subset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i]:
% 1.06/1.24     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.06/1.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.06/1.24       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.06/1.24  thf('49', plain,
% 1.06/1.24      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 1.06/1.24          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 1.06/1.24          | ((k4_subset_1 @ X32 @ X31 @ X33) = (k2_xboole_0 @ X31 @ X33)))),
% 1.06/1.24      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.06/1.24  thf('50', plain,
% 1.06/1.24      ((![X0 : $i]:
% 1.06/1.24          (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.06/1.24             = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 1.06/1.24           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup-', [status(thm)], ['48', '49'])).
% 1.06/1.24  thf('51', plain,
% 1.06/1.24      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.24          (k1_tops_1 @ sk_A @ sk_B))
% 1.06/1.24          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.24             (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup-', [status(thm)], ['43', '50'])).
% 1.06/1.24  thf(commutativity_k2_tarski, axiom,
% 1.06/1.24    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.06/1.24  thf('52', plain,
% 1.06/1.24      (![X15 : $i, X16 : $i]:
% 1.06/1.24         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 1.06/1.24      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.06/1.24  thf(l51_zfmisc_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.06/1.24  thf('53', plain,
% 1.06/1.24      (![X17 : $i, X18 : $i]:
% 1.06/1.24         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 1.06/1.24      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.06/1.24  thf('54', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.06/1.24      inference('sup+', [status(thm)], ['52', '53'])).
% 1.06/1.24  thf('55', plain,
% 1.06/1.24      (![X17 : $i, X18 : $i]:
% 1.06/1.24         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 1.06/1.24      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.06/1.24  thf('56', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.06/1.24      inference('sup+', [status(thm)], ['54', '55'])).
% 1.06/1.24  thf('57', plain,
% 1.06/1.24      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.24          (k1_tops_1 @ sk_A @ sk_B))
% 1.06/1.24          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.24             (k2_tops_1 @ sk_A @ sk_B))))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('demod', [status(thm)], ['51', '56'])).
% 1.06/1.24  thf('58', plain,
% 1.06/1.24      (((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.24         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.24      inference('demod', [status(thm)], ['4', '5', '10'])).
% 1.06/1.24  thf('59', plain,
% 1.06/1.24      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup+', [status(thm)], ['46', '47'])).
% 1.06/1.24  thf(t25_subset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.24       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.06/1.24         ( k2_subset_1 @ A ) ) ))).
% 1.06/1.24  thf('60', plain,
% 1.06/1.24      (![X39 : $i, X40 : $i]:
% 1.06/1.24         (((k4_subset_1 @ X39 @ X40 @ (k3_subset_1 @ X39 @ X40))
% 1.06/1.24            = (k2_subset_1 @ X39))
% 1.06/1.24          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 1.06/1.24      inference('cnf', [status(esa)], [t25_subset_1])).
% 1.06/1.24  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.06/1.24  thf('61', plain, (![X19 : $i]: ((k2_subset_1 @ X19) = (X19))),
% 1.06/1.24      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.06/1.24  thf('62', plain,
% 1.06/1.24      (![X39 : $i, X40 : $i]:
% 1.06/1.24         (((k4_subset_1 @ X39 @ X40 @ (k3_subset_1 @ X39 @ X40)) = (X39))
% 1.06/1.24          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 1.06/1.24      inference('demod', [status(thm)], ['60', '61'])).
% 1.06/1.24  thf('63', plain,
% 1.06/1.24      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.24          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup-', [status(thm)], ['59', '62'])).
% 1.06/1.24  thf('64', plain,
% 1.06/1.24      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup+', [status(thm)], ['46', '47'])).
% 1.06/1.24  thf('65', plain,
% 1.06/1.24      (![X20 : $i, X21 : $i]:
% 1.06/1.24         (((k3_subset_1 @ X20 @ X21) = (k6_subset_1 @ X20 @ X21))
% 1.06/1.24          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 1.06/1.24      inference('demod', [status(thm)], ['14', '15'])).
% 1.06/1.24  thf('66', plain,
% 1.06/1.24      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.24          = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup-', [status(thm)], ['64', '65'])).
% 1.06/1.24  thf('67', plain,
% 1.06/1.24      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.24          (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('demod', [status(thm)], ['63', '66'])).
% 1.06/1.24  thf('68', plain,
% 1.06/1.24      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.24          (k1_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup+', [status(thm)], ['58', '67'])).
% 1.06/1.24  thf('69', plain,
% 1.06/1.24      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.24          = (sk_B)))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup+', [status(thm)], ['57', '68'])).
% 1.06/1.24  thf('70', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.06/1.24      inference('sup+', [status(thm)], ['54', '55'])).
% 1.06/1.24  thf(t6_xboole_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.06/1.24  thf('71', plain,
% 1.06/1.24      (![X13 : $i, X14 : $i]:
% 1.06/1.24         ((k2_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14))
% 1.06/1.24           = (k2_xboole_0 @ X13 @ X14))),
% 1.06/1.24      inference('cnf', [status(esa)], [t6_xboole_1])).
% 1.06/1.24  thf('72', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.06/1.24           = (k2_xboole_0 @ X0 @ X1))),
% 1.06/1.24      inference('sup+', [status(thm)], ['70', '71'])).
% 1.06/1.24  thf('73', plain,
% 1.06/1.24      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.06/1.24          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.24             (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup+', [status(thm)], ['69', '72'])).
% 1.06/1.24  thf('74', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.06/1.24      inference('sup+', [status(thm)], ['54', '55'])).
% 1.06/1.24  thf('75', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(t65_tops_1, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( l1_pre_topc @ A ) =>
% 1.06/1.24       ( ![B:$i]:
% 1.06/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.24           ( ( k2_pre_topc @ A @ B ) =
% 1.06/1.24             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.06/1.24  thf('76', plain,
% 1.06/1.24      (![X52 : $i, X53 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 1.06/1.24          | ((k2_pre_topc @ X53 @ X52)
% 1.06/1.24              = (k4_subset_1 @ (u1_struct_0 @ X53) @ X52 @ 
% 1.06/1.24                 (k2_tops_1 @ X53 @ X52)))
% 1.06/1.24          | ~ (l1_pre_topc @ X53))),
% 1.06/1.24      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.06/1.24  thf('77', plain,
% 1.06/1.24      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.24        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.06/1.24            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.06/1.24      inference('sup-', [status(thm)], ['75', '76'])).
% 1.06/1.24  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('79', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(dt_k2_tops_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( ( l1_pre_topc @ A ) & 
% 1.06/1.24         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.24       ( m1_subset_1 @
% 1.06/1.24         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.06/1.24  thf('80', plain,
% 1.06/1.24      (![X48 : $i, X49 : $i]:
% 1.06/1.24         (~ (l1_pre_topc @ X48)
% 1.06/1.24          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 1.06/1.24          | (m1_subset_1 @ (k2_tops_1 @ X48 @ X49) @ 
% 1.06/1.24             (k1_zfmisc_1 @ (u1_struct_0 @ X48))))),
% 1.06/1.24      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.06/1.24  thf('81', plain,
% 1.06/1.24      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.24         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.24        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['79', '80'])).
% 1.06/1.24  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('83', plain,
% 1.06/1.24      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.24      inference('demod', [status(thm)], ['81', '82'])).
% 1.06/1.24  thf('84', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('85', plain,
% 1.06/1.24      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 1.06/1.24          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 1.06/1.24          | ((k4_subset_1 @ X32 @ X31 @ X33) = (k2_xboole_0 @ X31 @ X33)))),
% 1.06/1.24      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.06/1.24  thf('86', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.24            = (k2_xboole_0 @ sk_B @ X0))
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.06/1.24      inference('sup-', [status(thm)], ['84', '85'])).
% 1.06/1.24  thf('87', plain,
% 1.06/1.24      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.24         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['83', '86'])).
% 1.06/1.24  thf('88', plain,
% 1.06/1.24      (((k2_pre_topc @ sk_A @ sk_B)
% 1.06/1.24         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.24      inference('demod', [status(thm)], ['77', '78', '87'])).
% 1.06/1.24  thf('89', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.06/1.24      inference('sup+', [status(thm)], ['54', '55'])).
% 1.06/1.24  thf('90', plain,
% 1.06/1.24      ((((k2_pre_topc @ sk_A @ sk_B)
% 1.06/1.24          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.24             (k2_tops_1 @ sk_A @ sk_B))))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('demod', [status(thm)], ['73', '74', '88', '89'])).
% 1.06/1.24  thf('91', plain,
% 1.06/1.24      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.24          = (sk_B)))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup+', [status(thm)], ['57', '68'])).
% 1.06/1.24  thf('92', plain,
% 1.06/1.24      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup+', [status(thm)], ['90', '91'])).
% 1.06/1.24  thf('93', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(t52_pre_topc, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( l1_pre_topc @ A ) =>
% 1.06/1.24       ( ![B:$i]:
% 1.06/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.24           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.06/1.24             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.06/1.24               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.06/1.24  thf('94', plain,
% 1.06/1.24      (![X46 : $i, X47 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.06/1.24          | ~ (v2_pre_topc @ X47)
% 1.06/1.24          | ((k2_pre_topc @ X47 @ X46) != (X46))
% 1.06/1.24          | (v4_pre_topc @ X46 @ X47)
% 1.06/1.24          | ~ (l1_pre_topc @ X47))),
% 1.06/1.24      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.06/1.24  thf('95', plain,
% 1.06/1.24      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.24        | (v4_pre_topc @ sk_B @ sk_A)
% 1.06/1.24        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 1.06/1.24        | ~ (v2_pre_topc @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['93', '94'])).
% 1.06/1.24  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('98', plain,
% 1.06/1.24      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 1.06/1.24      inference('demod', [status(thm)], ['95', '96', '97'])).
% 1.06/1.24  thf('99', plain,
% 1.06/1.24      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('sup-', [status(thm)], ['92', '98'])).
% 1.06/1.24  thf('100', plain,
% 1.06/1.24      (((v4_pre_topc @ sk_B @ sk_A))
% 1.06/1.24         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.24      inference('simplify', [status(thm)], ['99'])).
% 1.06/1.24  thf('101', plain,
% 1.06/1.24      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.24      inference('split', [status(esa)], ['0'])).
% 1.06/1.24  thf('102', plain,
% 1.06/1.24      (~
% 1.06/1.24       (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.24          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.24             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.06/1.24       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['100', '101'])).
% 1.06/1.24  thf('103', plain, ($false),
% 1.06/1.24      inference('sat_resolution*', [status(thm)], ['1', '41', '42', '102'])).
% 1.06/1.24  
% 1.06/1.24  % SZS output end Refutation
% 1.06/1.24  
% 1.09/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
