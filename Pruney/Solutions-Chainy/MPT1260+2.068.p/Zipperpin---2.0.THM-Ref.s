%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tqUuVZQBo7

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:33 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 427 expanded)
%              Number of leaves         :   29 ( 138 expanded)
%              Depth                    :   16
%              Number of atoms          : 1289 (5033 expanded)
%              Number of equality atoms :   67 ( 214 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v3_pre_topc @ X36 @ X37 )
      | ~ ( r1_tarski @ X36 @ X38 )
      | ( r1_tarski @ X36 @ ( k1_tops_1 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('16',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X35 @ X34 ) @ X34 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k2_tops_1 @ X33 @ X32 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X33 ) @ ( k2_pre_topc @ X33 @ X32 ) @ ( k1_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('43',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('47',plain,
    ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('50',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('52',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','50','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('58',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_tarski @ X28 @ ( k2_pre_topc @ X29 @ X28 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('65',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('68',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('70',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['65','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('72',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X10 @ X9 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('75',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['70','77'])).

thf('79',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['70','77'])).

thf('82',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['80','83','84'])).

thf('86',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['56','85'])).

thf('87',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('88',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','50','55'])).

thf('89',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('91',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('92',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['65','68','69'])).

thf('94',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('97',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X30 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('98',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['95','101'])).

thf('103',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','41','42','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tqUuVZQBo7
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:31:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.11/2.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.11/2.32  % Solved by: fo/fo7.sh
% 2.11/2.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.11/2.32  % done 3078 iterations in 1.867s
% 2.11/2.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.11/2.32  % SZS output start Refutation
% 2.11/2.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.11/2.32  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.11/2.32  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.11/2.32  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 2.11/2.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.11/2.32  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.11/2.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.11/2.32  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.11/2.32  thf(sk_A_type, type, sk_A: $i).
% 2.11/2.32  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.11/2.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.11/2.32  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.11/2.32  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.11/2.32  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.11/2.32  thf(sk_B_type, type, sk_B: $i).
% 2.11/2.32  thf(t76_tops_1, conjecture,
% 2.11/2.32    (![A:$i]:
% 2.11/2.32     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.11/2.32       ( ![B:$i]:
% 2.11/2.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.11/2.32           ( ( v3_pre_topc @ B @ A ) <=>
% 2.11/2.32             ( ( k2_tops_1 @ A @ B ) =
% 2.11/2.32               ( k7_subset_1 @
% 2.11/2.32                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 2.11/2.32  thf(zf_stmt_0, negated_conjecture,
% 2.11/2.32    (~( ![A:$i]:
% 2.11/2.32        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.11/2.32          ( ![B:$i]:
% 2.11/2.32            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.11/2.32              ( ( v3_pre_topc @ B @ A ) <=>
% 2.11/2.32                ( ( k2_tops_1 @ A @ B ) =
% 2.11/2.32                  ( k7_subset_1 @
% 2.11/2.32                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 2.11/2.32    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 2.11/2.32  thf('0', plain,
% 2.11/2.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 2.11/2.32        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf('1', plain,
% 2.11/2.32      (~
% 2.11/2.32       (((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 2.11/2.32       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 2.11/2.32      inference('split', [status(esa)], ['0'])).
% 2.11/2.32  thf('2', plain,
% 2.11/2.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf('3', plain,
% 2.11/2.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 2.11/2.32        | (v3_pre_topc @ sk_B @ sk_A))),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf('4', plain,
% 2.11/2.32      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.11/2.32      inference('split', [status(esa)], ['3'])).
% 2.11/2.32  thf('5', plain,
% 2.11/2.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf(t56_tops_1, axiom,
% 2.11/2.32    (![A:$i]:
% 2.11/2.32     ( ( l1_pre_topc @ A ) =>
% 2.11/2.32       ( ![B:$i]:
% 2.11/2.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.11/2.32           ( ![C:$i]:
% 2.11/2.32             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.11/2.32               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 2.11/2.32                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.11/2.32  thf('6', plain,
% 2.11/2.32      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.11/2.32         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 2.11/2.32          | ~ (v3_pre_topc @ X36 @ X37)
% 2.11/2.32          | ~ (r1_tarski @ X36 @ X38)
% 2.11/2.32          | (r1_tarski @ X36 @ (k1_tops_1 @ X37 @ X38))
% 2.11/2.32          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 2.11/2.32          | ~ (l1_pre_topc @ X37))),
% 2.11/2.32      inference('cnf', [status(esa)], [t56_tops_1])).
% 2.11/2.32  thf('7', plain,
% 2.11/2.32      (![X0 : $i]:
% 2.11/2.32         (~ (l1_pre_topc @ sk_A)
% 2.11/2.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.11/2.32          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 2.11/2.32          | ~ (r1_tarski @ sk_B @ X0)
% 2.11/2.32          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 2.11/2.32      inference('sup-', [status(thm)], ['5', '6'])).
% 2.11/2.32  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf('9', plain,
% 2.11/2.32      (![X0 : $i]:
% 2.11/2.32         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.11/2.32          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 2.11/2.32          | ~ (r1_tarski @ sk_B @ X0)
% 2.11/2.32          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 2.11/2.32      inference('demod', [status(thm)], ['7', '8'])).
% 2.11/2.32  thf('10', plain,
% 2.11/2.32      ((![X0 : $i]:
% 2.11/2.32          (~ (r1_tarski @ sk_B @ X0)
% 2.11/2.32           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 2.11/2.32           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 2.11/2.32         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.11/2.32      inference('sup-', [status(thm)], ['4', '9'])).
% 2.11/2.32  thf('11', plain,
% 2.11/2.32      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.11/2.32         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.11/2.32      inference('sup-', [status(thm)], ['2', '10'])).
% 2.11/2.32  thf(d10_xboole_0, axiom,
% 2.11/2.32    (![A:$i,B:$i]:
% 2.11/2.32     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.11/2.32  thf('12', plain,
% 2.11/2.32      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.11/2.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.11/2.32  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.11/2.32      inference('simplify', [status(thm)], ['12'])).
% 2.11/2.32  thf('14', plain,
% 2.11/2.32      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 2.11/2.32         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.11/2.32      inference('demod', [status(thm)], ['11', '13'])).
% 2.11/2.32  thf('15', plain,
% 2.11/2.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf(t44_tops_1, axiom,
% 2.11/2.32    (![A:$i]:
% 2.11/2.32     ( ( l1_pre_topc @ A ) =>
% 2.11/2.32       ( ![B:$i]:
% 2.11/2.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.11/2.32           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 2.11/2.32  thf('16', plain,
% 2.11/2.32      (![X34 : $i, X35 : $i]:
% 2.11/2.32         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 2.11/2.32          | (r1_tarski @ (k1_tops_1 @ X35 @ X34) @ X34)
% 2.11/2.32          | ~ (l1_pre_topc @ X35))),
% 2.11/2.32      inference('cnf', [status(esa)], [t44_tops_1])).
% 2.11/2.32  thf('17', plain,
% 2.11/2.32      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 2.11/2.32      inference('sup-', [status(thm)], ['15', '16'])).
% 2.11/2.32  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf('19', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 2.11/2.32      inference('demod', [status(thm)], ['17', '18'])).
% 2.11/2.32  thf('20', plain,
% 2.11/2.32      (![X0 : $i, X2 : $i]:
% 2.11/2.32         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.11/2.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.11/2.32  thf('21', plain,
% 2.11/2.32      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.11/2.32        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 2.11/2.32      inference('sup-', [status(thm)], ['19', '20'])).
% 2.11/2.32  thf('22', plain,
% 2.11/2.32      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 2.11/2.32         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.11/2.32      inference('sup-', [status(thm)], ['14', '21'])).
% 2.11/2.32  thf('23', plain,
% 2.11/2.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf(l78_tops_1, axiom,
% 2.11/2.32    (![A:$i]:
% 2.11/2.32     ( ( l1_pre_topc @ A ) =>
% 2.11/2.32       ( ![B:$i]:
% 2.11/2.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.11/2.32           ( ( k2_tops_1 @ A @ B ) =
% 2.11/2.32             ( k7_subset_1 @
% 2.11/2.32               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 2.11/2.32               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.11/2.32  thf('24', plain,
% 2.11/2.32      (![X32 : $i, X33 : $i]:
% 2.11/2.32         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 2.11/2.32          | ((k2_tops_1 @ X33 @ X32)
% 2.11/2.32              = (k7_subset_1 @ (u1_struct_0 @ X33) @ 
% 2.11/2.32                 (k2_pre_topc @ X33 @ X32) @ (k1_tops_1 @ X33 @ X32)))
% 2.11/2.32          | ~ (l1_pre_topc @ X33))),
% 2.11/2.32      inference('cnf', [status(esa)], [l78_tops_1])).
% 2.11/2.32  thf('25', plain,
% 2.11/2.32      ((~ (l1_pre_topc @ sk_A)
% 2.11/2.32        | ((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 2.11/2.32      inference('sup-', [status(thm)], ['23', '24'])).
% 2.11/2.32  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf('27', plain,
% 2.11/2.32      (((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.11/2.32      inference('demod', [status(thm)], ['25', '26'])).
% 2.11/2.32  thf('28', plain,
% 2.11/2.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf(dt_k2_pre_topc, axiom,
% 2.11/2.32    (![A:$i,B:$i]:
% 2.11/2.32     ( ( ( l1_pre_topc @ A ) & 
% 2.11/2.32         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.11/2.32       ( m1_subset_1 @
% 2.11/2.32         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.11/2.32  thf('29', plain,
% 2.11/2.32      (![X26 : $i, X27 : $i]:
% 2.11/2.32         (~ (l1_pre_topc @ X26)
% 2.11/2.32          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 2.11/2.32          | (m1_subset_1 @ (k2_pre_topc @ X26 @ X27) @ 
% 2.11/2.32             (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 2.11/2.32      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.11/2.32  thf('30', plain,
% 2.11/2.32      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.11/2.32        | ~ (l1_pre_topc @ sk_A))),
% 2.11/2.32      inference('sup-', [status(thm)], ['28', '29'])).
% 2.11/2.32  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf('32', plain,
% 2.11/2.32      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.11/2.32      inference('demod', [status(thm)], ['30', '31'])).
% 2.11/2.32  thf(redefinition_k7_subset_1, axiom,
% 2.11/2.32    (![A:$i,B:$i,C:$i]:
% 2.11/2.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.11/2.32       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.11/2.32  thf('33', plain,
% 2.11/2.32      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.11/2.32         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 2.11/2.32          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 2.11/2.32      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.11/2.32  thf('34', plain,
% 2.11/2.32      (![X0 : $i]:
% 2.11/2.32         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 2.11/2.32      inference('sup-', [status(thm)], ['32', '33'])).
% 2.11/2.32  thf('35', plain,
% 2.11/2.32      (((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.11/2.32      inference('demod', [status(thm)], ['27', '34'])).
% 2.11/2.32  thf('36', plain,
% 2.11/2.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.11/2.32         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 2.11/2.32      inference('sup+', [status(thm)], ['22', '35'])).
% 2.11/2.32  thf('37', plain,
% 2.11/2.32      (![X0 : $i]:
% 2.11/2.32         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 2.11/2.32      inference('sup-', [status(thm)], ['32', '33'])).
% 2.11/2.32  thf('38', plain,
% 2.11/2.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.11/2.32         <= (~
% 2.11/2.32             (((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.11/2.32      inference('split', [status(esa)], ['0'])).
% 2.11/2.32  thf('39', plain,
% 2.11/2.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.11/2.32         <= (~
% 2.11/2.32             (((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.11/2.32      inference('sup-', [status(thm)], ['37', '38'])).
% 2.11/2.32  thf('40', plain,
% 2.11/2.32      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 2.11/2.32         <= (~
% 2.11/2.32             (((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 2.11/2.32             ((v3_pre_topc @ sk_B @ sk_A)))),
% 2.11/2.32      inference('sup-', [status(thm)], ['36', '39'])).
% 2.11/2.32  thf('41', plain,
% 2.11/2.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 2.11/2.32       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 2.11/2.32      inference('simplify', [status(thm)], ['40'])).
% 2.11/2.32  thf('42', plain,
% 2.11/2.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 2.11/2.32       ((v3_pre_topc @ sk_B @ sk_A))),
% 2.11/2.32      inference('split', [status(esa)], ['3'])).
% 2.11/2.32  thf('43', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 2.11/2.32      inference('demod', [status(thm)], ['17', '18'])).
% 2.11/2.32  thf(t3_subset, axiom,
% 2.11/2.32    (![A:$i,B:$i]:
% 2.11/2.32     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.11/2.32  thf('44', plain,
% 2.11/2.32      (![X23 : $i, X25 : $i]:
% 2.11/2.32         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 2.11/2.32      inference('cnf', [status(esa)], [t3_subset])).
% 2.11/2.32  thf('45', plain,
% 2.11/2.32      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 2.11/2.32      inference('sup-', [status(thm)], ['43', '44'])).
% 2.11/2.32  thf(involutiveness_k3_subset_1, axiom,
% 2.11/2.32    (![A:$i,B:$i]:
% 2.11/2.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.11/2.32       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 2.11/2.32  thf('46', plain,
% 2.11/2.32      (![X15 : $i, X16 : $i]:
% 2.11/2.32         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 2.11/2.32          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 2.11/2.32      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.11/2.32  thf('47', plain,
% 2.11/2.32      (((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 2.11/2.32         = (k1_tops_1 @ sk_A @ sk_B))),
% 2.11/2.32      inference('sup-', [status(thm)], ['45', '46'])).
% 2.11/2.32  thf('48', plain,
% 2.11/2.32      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 2.11/2.32      inference('sup-', [status(thm)], ['43', '44'])).
% 2.11/2.32  thf(d5_subset_1, axiom,
% 2.11/2.32    (![A:$i,B:$i]:
% 2.11/2.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.11/2.32       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.11/2.32  thf('49', plain,
% 2.11/2.32      (![X5 : $i, X6 : $i]:
% 2.11/2.32         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 2.11/2.32          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 2.11/2.32      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.11/2.32  thf('50', plain,
% 2.11/2.32      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.11/2.32         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.11/2.32      inference('sup-', [status(thm)], ['48', '49'])).
% 2.11/2.32  thf(t36_xboole_1, axiom,
% 2.11/2.32    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.11/2.32  thf('51', plain,
% 2.11/2.32      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 2.11/2.32      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.11/2.32  thf('52', plain,
% 2.11/2.32      (![X23 : $i, X25 : $i]:
% 2.11/2.32         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 2.11/2.32      inference('cnf', [status(esa)], [t3_subset])).
% 2.11/2.32  thf('53', plain,
% 2.11/2.32      (![X0 : $i, X1 : $i]:
% 2.11/2.32         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.11/2.32      inference('sup-', [status(thm)], ['51', '52'])).
% 2.11/2.32  thf('54', plain,
% 2.11/2.32      (![X5 : $i, X6 : $i]:
% 2.11/2.32         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 2.11/2.32          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 2.11/2.32      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.11/2.32  thf('55', plain,
% 2.11/2.32      (![X0 : $i, X1 : $i]:
% 2.11/2.32         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.11/2.32           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.11/2.32      inference('sup-', [status(thm)], ['53', '54'])).
% 2.11/2.32  thf('56', plain,
% 2.11/2.32      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 2.11/2.32         = (k1_tops_1 @ sk_A @ sk_B))),
% 2.11/2.32      inference('demod', [status(thm)], ['47', '50', '55'])).
% 2.11/2.32  thf('57', plain,
% 2.11/2.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf(t48_pre_topc, axiom,
% 2.11/2.32    (![A:$i]:
% 2.11/2.32     ( ( l1_pre_topc @ A ) =>
% 2.11/2.32       ( ![B:$i]:
% 2.11/2.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.11/2.32           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 2.11/2.32  thf('58', plain,
% 2.11/2.32      (![X28 : $i, X29 : $i]:
% 2.11/2.32         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 2.11/2.32          | (r1_tarski @ X28 @ (k2_pre_topc @ X29 @ X28))
% 2.11/2.32          | ~ (l1_pre_topc @ X29))),
% 2.11/2.32      inference('cnf', [status(esa)], [t48_pre_topc])).
% 2.11/2.32  thf('59', plain,
% 2.11/2.32      ((~ (l1_pre_topc @ sk_A)
% 2.11/2.32        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.11/2.32      inference('sup-', [status(thm)], ['57', '58'])).
% 2.11/2.32  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf('61', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 2.11/2.32      inference('demod', [status(thm)], ['59', '60'])).
% 2.11/2.32  thf('62', plain,
% 2.11/2.32      (![X23 : $i, X25 : $i]:
% 2.11/2.32         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 2.11/2.32      inference('cnf', [status(esa)], [t3_subset])).
% 2.11/2.32  thf('63', plain,
% 2.11/2.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.11/2.32      inference('sup-', [status(thm)], ['61', '62'])).
% 2.11/2.32  thf('64', plain,
% 2.11/2.32      (![X15 : $i, X16 : $i]:
% 2.11/2.32         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 2.11/2.32          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 2.11/2.32      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.11/2.32  thf('65', plain,
% 2.11/2.32      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 2.11/2.32      inference('sup-', [status(thm)], ['63', '64'])).
% 2.11/2.32  thf('66', plain,
% 2.11/2.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.11/2.32      inference('sup-', [status(thm)], ['61', '62'])).
% 2.11/2.32  thf('67', plain,
% 2.11/2.32      (![X5 : $i, X6 : $i]:
% 2.11/2.32         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 2.11/2.32          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 2.11/2.32      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.11/2.32  thf('68', plain,
% 2.11/2.32      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 2.11/2.32         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 2.11/2.32      inference('sup-', [status(thm)], ['66', '67'])).
% 2.11/2.32  thf('69', plain,
% 2.11/2.32      (![X0 : $i, X1 : $i]:
% 2.11/2.32         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.11/2.32           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.11/2.32      inference('sup-', [status(thm)], ['53', '54'])).
% 2.11/2.32  thf('70', plain,
% 2.11/2.32      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 2.11/2.32      inference('demod', [status(thm)], ['65', '68', '69'])).
% 2.11/2.32  thf('71', plain,
% 2.11/2.32      (![X0 : $i, X1 : $i]:
% 2.11/2.32         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.11/2.32      inference('sup-', [status(thm)], ['51', '52'])).
% 2.11/2.32  thf(dt_k7_subset_1, axiom,
% 2.11/2.32    (![A:$i,B:$i,C:$i]:
% 2.11/2.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.11/2.32       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.11/2.32  thf('72', plain,
% 2.11/2.32      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.11/2.32         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 2.11/2.32          | (m1_subset_1 @ (k7_subset_1 @ X10 @ X9 @ X11) @ (k1_zfmisc_1 @ X10)))),
% 2.11/2.32      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 2.11/2.32  thf('73', plain,
% 2.11/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.32         (m1_subset_1 @ (k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ 
% 2.11/2.32          (k1_zfmisc_1 @ X0))),
% 2.11/2.32      inference('sup-', [status(thm)], ['71', '72'])).
% 2.11/2.32  thf('74', plain,
% 2.11/2.32      (![X0 : $i, X1 : $i]:
% 2.11/2.32         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.11/2.32      inference('sup-', [status(thm)], ['51', '52'])).
% 2.11/2.32  thf('75', plain,
% 2.11/2.32      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.11/2.32         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 2.11/2.32          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 2.11/2.32      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.11/2.32  thf('76', plain,
% 2.11/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.32         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 2.11/2.32           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 2.11/2.32      inference('sup-', [status(thm)], ['74', '75'])).
% 2.11/2.32  thf('77', plain,
% 2.11/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.11/2.32         (m1_subset_1 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ 
% 2.11/2.32          (k1_zfmisc_1 @ X0))),
% 2.11/2.32      inference('demod', [status(thm)], ['73', '76'])).
% 2.11/2.32  thf('78', plain,
% 2.11/2.32      (![X0 : $i]:
% 2.11/2.32         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 2.11/2.32          (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.11/2.32      inference('sup+', [status(thm)], ['70', '77'])).
% 2.11/2.32  thf('79', plain,
% 2.11/2.32      (![X15 : $i, X16 : $i]:
% 2.11/2.32         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 2.11/2.32          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 2.11/2.32      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.11/2.32  thf('80', plain,
% 2.11/2.32      (![X0 : $i]:
% 2.11/2.32         ((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32           (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32            (k4_xboole_0 @ sk_B @ X0)))
% 2.11/2.32           = (k4_xboole_0 @ sk_B @ X0))),
% 2.11/2.32      inference('sup-', [status(thm)], ['78', '79'])).
% 2.11/2.32  thf('81', plain,
% 2.11/2.32      (![X0 : $i]:
% 2.11/2.32         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 2.11/2.32          (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.11/2.32      inference('sup+', [status(thm)], ['70', '77'])).
% 2.11/2.32  thf('82', plain,
% 2.11/2.32      (![X5 : $i, X6 : $i]:
% 2.11/2.32         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 2.11/2.32          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 2.11/2.32      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.11/2.32  thf('83', plain,
% 2.11/2.32      (![X0 : $i]:
% 2.11/2.32         ((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32           (k4_xboole_0 @ sk_B @ X0))
% 2.11/2.32           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32              (k4_xboole_0 @ sk_B @ X0)))),
% 2.11/2.32      inference('sup-', [status(thm)], ['81', '82'])).
% 2.11/2.32  thf('84', plain,
% 2.11/2.32      (![X0 : $i, X1 : $i]:
% 2.11/2.32         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.11/2.32           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.11/2.32      inference('sup-', [status(thm)], ['53', '54'])).
% 2.11/2.32  thf('85', plain,
% 2.11/2.32      (![X0 : $i]:
% 2.11/2.32         ((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32           (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32            (k4_xboole_0 @ sk_B @ X0)))
% 2.11/2.32           = (k4_xboole_0 @ sk_B @ X0))),
% 2.11/2.32      inference('demod', [status(thm)], ['80', '83', '84'])).
% 2.11/2.32  thf('86', plain,
% 2.11/2.32      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))
% 2.11/2.32         = (k4_xboole_0 @ sk_B @ 
% 2.11/2.32            (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 2.11/2.32      inference('sup+', [status(thm)], ['56', '85'])).
% 2.11/2.32  thf('87', plain,
% 2.11/2.32      (((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32            (k1_tops_1 @ sk_A @ sk_B)))),
% 2.11/2.32      inference('demod', [status(thm)], ['27', '34'])).
% 2.11/2.32  thf('88', plain,
% 2.11/2.32      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 2.11/2.32         = (k1_tops_1 @ sk_A @ sk_B))),
% 2.11/2.32      inference('demod', [status(thm)], ['47', '50', '55'])).
% 2.11/2.32  thf('89', plain,
% 2.11/2.32      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 2.11/2.32         = (k1_tops_1 @ sk_A @ sk_B))),
% 2.11/2.32      inference('demod', [status(thm)], ['86', '87', '88'])).
% 2.11/2.32  thf('90', plain,
% 2.11/2.32      (![X0 : $i]:
% 2.11/2.32         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 2.11/2.32      inference('sup-', [status(thm)], ['32', '33'])).
% 2.11/2.32  thf('91', plain,
% 2.11/2.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.11/2.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.11/2.32      inference('split', [status(esa)], ['3'])).
% 2.11/2.32  thf('92', plain,
% 2.11/2.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 2.11/2.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.11/2.32      inference('sup+', [status(thm)], ['90', '91'])).
% 2.11/2.32  thf('93', plain,
% 2.11/2.32      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.11/2.32         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 2.11/2.32      inference('demod', [status(thm)], ['65', '68', '69'])).
% 2.11/2.32  thf('94', plain,
% 2.11/2.32      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 2.11/2.32          = (sk_B)))
% 2.11/2.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.11/2.32      inference('sup+', [status(thm)], ['92', '93'])).
% 2.11/2.32  thf('95', plain,
% 2.11/2.32      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 2.11/2.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.11/2.32      inference('sup+', [status(thm)], ['89', '94'])).
% 2.11/2.32  thf('96', plain,
% 2.11/2.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf(fc9_tops_1, axiom,
% 2.11/2.32    (![A:$i,B:$i]:
% 2.11/2.32     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 2.11/2.32         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.11/2.32       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 2.11/2.32  thf('97', plain,
% 2.11/2.32      (![X30 : $i, X31 : $i]:
% 2.11/2.32         (~ (l1_pre_topc @ X30)
% 2.11/2.32          | ~ (v2_pre_topc @ X30)
% 2.11/2.32          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 2.11/2.32          | (v3_pre_topc @ (k1_tops_1 @ X30 @ X31) @ X30))),
% 2.11/2.32      inference('cnf', [status(esa)], [fc9_tops_1])).
% 2.11/2.32  thf('98', plain,
% 2.11/2.32      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 2.11/2.32        | ~ (v2_pre_topc @ sk_A)
% 2.11/2.32        | ~ (l1_pre_topc @ sk_A))),
% 2.11/2.32      inference('sup-', [status(thm)], ['96', '97'])).
% 2.11/2.32  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 2.11/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.11/2.32  thf('101', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 2.11/2.32      inference('demod', [status(thm)], ['98', '99', '100'])).
% 2.11/2.32  thf('102', plain,
% 2.11/2.32      (((v3_pre_topc @ sk_B @ sk_A))
% 2.11/2.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 2.11/2.32      inference('sup+', [status(thm)], ['95', '101'])).
% 2.11/2.32  thf('103', plain,
% 2.11/2.32      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 2.11/2.32      inference('split', [status(esa)], ['0'])).
% 2.11/2.32  thf('104', plain,
% 2.11/2.32      (~
% 2.11/2.32       (((k2_tops_1 @ sk_A @ sk_B)
% 2.11/2.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.11/2.32             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 2.11/2.32       ((v3_pre_topc @ sk_B @ sk_A))),
% 2.11/2.32      inference('sup-', [status(thm)], ['102', '103'])).
% 2.11/2.32  thf('105', plain, ($false),
% 2.11/2.32      inference('sat_resolution*', [status(thm)], ['1', '41', '42', '104'])).
% 2.11/2.32  
% 2.11/2.32  % SZS output end Refutation
% 2.11/2.32  
% 2.11/2.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
