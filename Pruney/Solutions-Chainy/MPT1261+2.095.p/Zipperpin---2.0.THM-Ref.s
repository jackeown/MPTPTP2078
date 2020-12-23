%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.atiIMPe0q1

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:52 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 578 expanded)
%              Number of leaves         :   38 ( 194 expanded)
%              Depth                    :   21
%              Number of atoms          : 1690 (5515 expanded)
%              Number of equality atoms :  142 ( 435 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X40 @ X39 ) @ X39 )
      | ~ ( v4_pre_topc @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
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
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('13',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k1_tops_1 @ X42 @ X41 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X42 ) @ X41 @ ( k2_tops_1 @ X42 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X25 @ X27 )
        = ( k4_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('32',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

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
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('41',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( k2_pre_topc @ X38 @ X37 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 @ ( k2_tops_1 @ X38 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('54',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('58',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('67',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('68',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('77',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','83'])).

thf('85',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['47','84'])).

thf('86',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
        | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('95',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('97',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('99',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_B @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('103',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('104',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['95','96'])).

thf('106',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('108',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','74'])).

thf('110',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('112',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('113',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_B @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('115',plain,
    ( ( k3_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('117',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['110','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('120',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['101','118','119'])).

thf('121',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('122',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['92','122'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('124',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k4_subset_1 @ X23 @ X22 @ X24 )
        = ( k2_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X1 )
        = ( k2_xboole_0 @ sk_B @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( k4_subset_1 @ ( k2_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['91','125'])).

thf('127',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('128',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['110','117'])).

thf('129',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('131',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('135',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132','133','134'])).

thf('136',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['47','84'])).

thf('137',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('138',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('141',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['126','135','141'])).

thf('143',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['44','142'])).

thf('144',plain,(
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

thf('145',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v2_pre_topc @ X34 )
      | ( ( k2_pre_topc @ X34 @ X33 )
       != X33 )
      | ( v4_pre_topc @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('146',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['143','149'])).

thf('151',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('153',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','38','39','153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.atiIMPe0q1
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:31:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.02/1.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.02/1.19  % Solved by: fo/fo7.sh
% 1.02/1.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.19  % done 2168 iterations in 0.737s
% 1.02/1.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.02/1.19  % SZS output start Refutation
% 1.02/1.19  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.02/1.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.02/1.19  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.02/1.19  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.02/1.19  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.02/1.19  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.19  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.02/1.19  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.02/1.19  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.02/1.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.02/1.19  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.02/1.19  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.02/1.19  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.02/1.19  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.02/1.19  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.02/1.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.02/1.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.02/1.19  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.19  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.02/1.19  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.02/1.19  thf(t77_tops_1, conjecture,
% 1.02/1.19    (![A:$i]:
% 1.02/1.19     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.19       ( ![B:$i]:
% 1.02/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.19           ( ( v4_pre_topc @ B @ A ) <=>
% 1.02/1.19             ( ( k2_tops_1 @ A @ B ) =
% 1.02/1.19               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.02/1.19  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.19    (~( ![A:$i]:
% 1.02/1.19        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.19          ( ![B:$i]:
% 1.02/1.19            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.19              ( ( v4_pre_topc @ B @ A ) <=>
% 1.02/1.19                ( ( k2_tops_1 @ A @ B ) =
% 1.02/1.19                  ( k7_subset_1 @
% 1.02/1.19                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.02/1.19    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.02/1.19  thf('0', plain,
% 1.02/1.19      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19              (k1_tops_1 @ sk_A @ sk_B)))
% 1.02/1.19        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('1', plain,
% 1.02/1.19      (~
% 1.02/1.19       (((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.02/1.19       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.02/1.19      inference('split', [status(esa)], ['0'])).
% 1.02/1.19  thf('2', plain,
% 1.02/1.19      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19             (k1_tops_1 @ sk_A @ sk_B)))
% 1.02/1.19        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('3', plain,
% 1.02/1.19      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.02/1.19      inference('split', [status(esa)], ['2'])).
% 1.02/1.19  thf('4', plain,
% 1.02/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf(t69_tops_1, axiom,
% 1.02/1.19    (![A:$i]:
% 1.02/1.19     ( ( l1_pre_topc @ A ) =>
% 1.02/1.19       ( ![B:$i]:
% 1.02/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.19           ( ( v4_pre_topc @ B @ A ) =>
% 1.02/1.19             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.02/1.19  thf('5', plain,
% 1.02/1.19      (![X39 : $i, X40 : $i]:
% 1.02/1.19         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.02/1.19          | (r1_tarski @ (k2_tops_1 @ X40 @ X39) @ X39)
% 1.02/1.19          | ~ (v4_pre_topc @ X39 @ X40)
% 1.02/1.19          | ~ (l1_pre_topc @ X40))),
% 1.02/1.19      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.02/1.19  thf('6', plain,
% 1.02/1.19      ((~ (l1_pre_topc @ sk_A)
% 1.02/1.19        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.02/1.19        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.02/1.19      inference('sup-', [status(thm)], ['4', '5'])).
% 1.02/1.19  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('8', plain,
% 1.02/1.19      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.02/1.19        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.02/1.19      inference('demod', [status(thm)], ['6', '7'])).
% 1.02/1.19  thf('9', plain,
% 1.02/1.19      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.02/1.19         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['3', '8'])).
% 1.02/1.19  thf(t3_subset, axiom,
% 1.02/1.19    (![A:$i,B:$i]:
% 1.02/1.19     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.02/1.19  thf('10', plain,
% 1.02/1.19      (![X30 : $i, X32 : $i]:
% 1.02/1.19         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 1.02/1.19      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.19  thf('11', plain,
% 1.02/1.19      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.02/1.19         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['9', '10'])).
% 1.02/1.19  thf(d5_subset_1, axiom,
% 1.02/1.19    (![A:$i,B:$i]:
% 1.02/1.19     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.19       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.02/1.19  thf('12', plain,
% 1.02/1.19      (![X18 : $i, X19 : $i]:
% 1.02/1.19         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 1.02/1.19          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 1.02/1.19      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.02/1.19  thf('13', plain,
% 1.02/1.19      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.02/1.19          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.02/1.19         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['11', '12'])).
% 1.02/1.19  thf(t48_xboole_1, axiom,
% 1.02/1.19    (![A:$i,B:$i]:
% 1.02/1.19     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.02/1.19  thf('14', plain,
% 1.02/1.19      (![X16 : $i, X17 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.02/1.19           = (k3_xboole_0 @ X16 @ X17))),
% 1.02/1.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.19  thf('15', plain,
% 1.02/1.19      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.19          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.02/1.19         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.02/1.19      inference('sup+', [status(thm)], ['13', '14'])).
% 1.02/1.19  thf('16', plain,
% 1.02/1.19      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.02/1.19         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['3', '8'])).
% 1.02/1.19  thf(t28_xboole_1, axiom,
% 1.02/1.19    (![A:$i,B:$i]:
% 1.02/1.19     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.02/1.19  thf('17', plain,
% 1.02/1.19      (![X7 : $i, X8 : $i]:
% 1.02/1.19         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 1.02/1.19      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.02/1.19  thf('18', plain,
% 1.02/1.19      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.02/1.19          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.19         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['16', '17'])).
% 1.02/1.19  thf(commutativity_k3_xboole_0, axiom,
% 1.02/1.19    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.02/1.19  thf('19', plain,
% 1.02/1.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.02/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.19  thf('20', plain,
% 1.02/1.19      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.02/1.19          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.19         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.02/1.19      inference('demod', [status(thm)], ['18', '19'])).
% 1.02/1.19  thf('21', plain,
% 1.02/1.19      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.19          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.19         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.02/1.19      inference('demod', [status(thm)], ['15', '20'])).
% 1.02/1.19  thf('22', plain,
% 1.02/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf(t74_tops_1, axiom,
% 1.02/1.19    (![A:$i]:
% 1.02/1.19     ( ( l1_pre_topc @ A ) =>
% 1.02/1.19       ( ![B:$i]:
% 1.02/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.19           ( ( k1_tops_1 @ A @ B ) =
% 1.02/1.19             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.02/1.19  thf('23', plain,
% 1.02/1.19      (![X41 : $i, X42 : $i]:
% 1.02/1.19         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 1.02/1.19          | ((k1_tops_1 @ X42 @ X41)
% 1.02/1.19              = (k7_subset_1 @ (u1_struct_0 @ X42) @ X41 @ 
% 1.02/1.19                 (k2_tops_1 @ X42 @ X41)))
% 1.02/1.19          | ~ (l1_pre_topc @ X42))),
% 1.02/1.19      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.02/1.19  thf('24', plain,
% 1.02/1.19      ((~ (l1_pre_topc @ sk_A)
% 1.02/1.19        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.02/1.19            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.02/1.19      inference('sup-', [status(thm)], ['22', '23'])).
% 1.02/1.19  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('26', plain,
% 1.02/1.19      (((k1_tops_1 @ sk_A @ sk_B)
% 1.02/1.19         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.02/1.19      inference('demod', [status(thm)], ['24', '25'])).
% 1.02/1.19  thf('27', plain,
% 1.02/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf(redefinition_k7_subset_1, axiom,
% 1.02/1.19    (![A:$i,B:$i,C:$i]:
% 1.02/1.19     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.19       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.02/1.19  thf('28', plain,
% 1.02/1.19      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.02/1.19         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 1.02/1.19          | ((k7_subset_1 @ X26 @ X25 @ X27) = (k4_xboole_0 @ X25 @ X27)))),
% 1.02/1.19      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.02/1.19  thf('29', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.02/1.19           = (k4_xboole_0 @ sk_B @ X0))),
% 1.02/1.19      inference('sup-', [status(thm)], ['27', '28'])).
% 1.02/1.19  thf('30', plain,
% 1.02/1.19      (((k1_tops_1 @ sk_A @ sk_B)
% 1.02/1.19         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.02/1.19      inference('demod', [status(thm)], ['26', '29'])).
% 1.02/1.19  thf('31', plain,
% 1.02/1.19      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.02/1.19          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.02/1.19         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['11', '12'])).
% 1.02/1.19  thf('32', plain,
% 1.02/1.19      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.02/1.19          = (k1_tops_1 @ sk_A @ sk_B)))
% 1.02/1.19         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.02/1.19      inference('sup+', [status(thm)], ['30', '31'])).
% 1.02/1.19  thf('33', plain,
% 1.02/1.19      ((((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.02/1.19          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.19         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.02/1.19      inference('demod', [status(thm)], ['21', '32'])).
% 1.02/1.19  thf('34', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.02/1.19           = (k4_xboole_0 @ sk_B @ X0))),
% 1.02/1.19      inference('sup-', [status(thm)], ['27', '28'])).
% 1.02/1.19  thf('35', plain,
% 1.02/1.19      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19              (k1_tops_1 @ sk_A @ sk_B))))
% 1.02/1.19         <= (~
% 1.02/1.19             (((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('split', [status(esa)], ['0'])).
% 1.02/1.19  thf('36', plain,
% 1.02/1.19      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.02/1.19         <= (~
% 1.02/1.19             (((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('sup-', [status(thm)], ['34', '35'])).
% 1.02/1.19  thf('37', plain,
% 1.02/1.19      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.19         <= (~
% 1.02/1.19             (((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.02/1.19             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['33', '36'])).
% 1.02/1.19  thf('38', plain,
% 1.02/1.19      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.02/1.19       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.02/1.19      inference('simplify', [status(thm)], ['37'])).
% 1.02/1.19  thf('39', plain,
% 1.02/1.19      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.02/1.19       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.02/1.19      inference('split', [status(esa)], ['2'])).
% 1.02/1.19  thf('40', plain,
% 1.02/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf(t65_tops_1, axiom,
% 1.02/1.19    (![A:$i]:
% 1.02/1.19     ( ( l1_pre_topc @ A ) =>
% 1.02/1.19       ( ![B:$i]:
% 1.02/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.19           ( ( k2_pre_topc @ A @ B ) =
% 1.02/1.19             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.02/1.19  thf('41', plain,
% 1.02/1.19      (![X37 : $i, X38 : $i]:
% 1.02/1.19         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.02/1.19          | ((k2_pre_topc @ X38 @ X37)
% 1.02/1.19              = (k4_subset_1 @ (u1_struct_0 @ X38) @ X37 @ 
% 1.02/1.19                 (k2_tops_1 @ X38 @ X37)))
% 1.02/1.19          | ~ (l1_pre_topc @ X38))),
% 1.02/1.19      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.02/1.19  thf('42', plain,
% 1.02/1.19      ((~ (l1_pre_topc @ sk_A)
% 1.02/1.19        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.02/1.19            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.02/1.19      inference('sup-', [status(thm)], ['40', '41'])).
% 1.02/1.19  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('44', plain,
% 1.02/1.19      (((k2_pre_topc @ sk_A @ sk_B)
% 1.02/1.19         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.02/1.19      inference('demod', [status(thm)], ['42', '43'])).
% 1.02/1.19  thf('45', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.02/1.19           = (k4_xboole_0 @ sk_B @ X0))),
% 1.02/1.19      inference('sup-', [status(thm)], ['27', '28'])).
% 1.02/1.19  thf('46', plain,
% 1.02/1.19      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19             (k1_tops_1 @ sk_A @ sk_B))))
% 1.02/1.19         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('split', [status(esa)], ['2'])).
% 1.02/1.19  thf('47', plain,
% 1.02/1.19      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.02/1.19         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('sup+', [status(thm)], ['45', '46'])).
% 1.02/1.19  thf(t36_xboole_1, axiom,
% 1.02/1.19    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.02/1.19  thf('48', plain,
% 1.02/1.19      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 1.02/1.19      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.02/1.19  thf('49', plain,
% 1.02/1.19      (![X7 : $i, X8 : $i]:
% 1.02/1.19         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 1.02/1.19      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.02/1.19  thf('50', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.02/1.19           = (k4_xboole_0 @ X0 @ X1))),
% 1.02/1.19      inference('sup-', [status(thm)], ['48', '49'])).
% 1.02/1.19  thf('51', plain,
% 1.02/1.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.02/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.19  thf('52', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.02/1.19           = (k4_xboole_0 @ X0 @ X1))),
% 1.02/1.19      inference('demod', [status(thm)], ['50', '51'])).
% 1.02/1.19  thf('53', plain,
% 1.02/1.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.02/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.19  thf(t100_xboole_1, axiom,
% 1.02/1.19    (![A:$i,B:$i]:
% 1.02/1.19     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.02/1.19  thf('54', plain,
% 1.02/1.19      (![X4 : $i, X5 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ X4 @ X5)
% 1.02/1.19           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.02/1.19      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.02/1.19  thf('55', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ X0 @ X1)
% 1.02/1.19           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.02/1.19      inference('sup+', [status(thm)], ['53', '54'])).
% 1.02/1.19  thf('56', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 1.02/1.19           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.02/1.19      inference('sup+', [status(thm)], ['52', '55'])).
% 1.02/1.19  thf(commutativity_k2_xboole_0, axiom,
% 1.02/1.19    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.02/1.19  thf('57', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.02/1.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.02/1.19  thf(t1_boole, axiom,
% 1.02/1.19    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.02/1.19  thf('58', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.02/1.19      inference('cnf', [status(esa)], [t1_boole])).
% 1.02/1.19  thf('59', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['57', '58'])).
% 1.02/1.19  thf(t39_xboole_1, axiom,
% 1.02/1.19    (![A:$i,B:$i]:
% 1.02/1.19     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.02/1.19  thf('60', plain,
% 1.02/1.19      (![X11 : $i, X12 : $i]:
% 1.02/1.19         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 1.02/1.19           = (k2_xboole_0 @ X11 @ X12))),
% 1.02/1.19      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.02/1.19  thf('61', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['59', '60'])).
% 1.02/1.19  thf('62', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['57', '58'])).
% 1.02/1.19  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.02/1.19      inference('demod', [status(thm)], ['61', '62'])).
% 1.02/1.19  thf('64', plain,
% 1.02/1.19      (![X16 : $i, X17 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.02/1.19           = (k3_xboole_0 @ X16 @ X17))),
% 1.02/1.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.19  thf('65', plain,
% 1.02/1.19      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['63', '64'])).
% 1.02/1.19  thf('66', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.02/1.19      inference('cnf', [status(esa)], [t1_boole])).
% 1.02/1.19  thf('67', plain,
% 1.02/1.19      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 1.02/1.19      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.02/1.19  thf(t44_xboole_1, axiom,
% 1.02/1.19    (![A:$i,B:$i,C:$i]:
% 1.02/1.19     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.02/1.19       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.02/1.19  thf('68', plain,
% 1.02/1.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.02/1.19         ((r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 1.02/1.19          | ~ (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15))),
% 1.02/1.19      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.02/1.19  thf('69', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.02/1.19      inference('sup-', [status(thm)], ['67', '68'])).
% 1.02/1.19  thf('70', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.02/1.19      inference('sup+', [status(thm)], ['66', '69'])).
% 1.02/1.19  thf('71', plain,
% 1.02/1.19      (![X7 : $i, X8 : $i]:
% 1.02/1.19         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 1.02/1.19      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.02/1.19  thf('72', plain,
% 1.02/1.19      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.02/1.19      inference('sup-', [status(thm)], ['70', '71'])).
% 1.02/1.19  thf('73', plain,
% 1.02/1.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.02/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.19  thf('74', plain,
% 1.02/1.19      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['72', '73'])).
% 1.02/1.19  thf('75', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.19      inference('demod', [status(thm)], ['65', '74'])).
% 1.02/1.19  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.02/1.19      inference('demod', [status(thm)], ['61', '62'])).
% 1.02/1.19  thf('77', plain,
% 1.02/1.19      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 1.02/1.19      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.02/1.19  thf('78', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.02/1.19      inference('sup+', [status(thm)], ['76', '77'])).
% 1.02/1.19  thf('79', plain,
% 1.02/1.19      (![X7 : $i, X8 : $i]:
% 1.02/1.19         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 1.02/1.19      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.02/1.19  thf('80', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.02/1.19      inference('sup-', [status(thm)], ['78', '79'])).
% 1.02/1.19  thf('81', plain,
% 1.02/1.19      (![X4 : $i, X5 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ X4 @ X5)
% 1.02/1.19           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.02/1.19      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.02/1.19  thf('82', plain,
% 1.02/1.19      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['80', '81'])).
% 1.02/1.19  thf('83', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.19      inference('demod', [status(thm)], ['75', '82'])).
% 1.02/1.19  thf('84', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.02/1.19      inference('demod', [status(thm)], ['56', '83'])).
% 1.02/1.19  thf('85', plain,
% 1.02/1.19      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.02/1.19         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('sup+', [status(thm)], ['47', '84'])).
% 1.02/1.19  thf('86', plain,
% 1.02/1.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.02/1.19         ((r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 1.02/1.19          | ~ (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15))),
% 1.02/1.19      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.02/1.19  thf('87', plain,
% 1.02/1.19      ((![X0 : $i]:
% 1.02/1.19          (~ (r1_tarski @ k1_xboole_0 @ X0)
% 1.02/1.19           | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_B @ X0))))
% 1.02/1.19         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('sup-', [status(thm)], ['85', '86'])).
% 1.02/1.19  thf('88', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.02/1.19      inference('sup+', [status(thm)], ['66', '69'])).
% 1.02/1.19  thf('89', plain,
% 1.02/1.19      ((![X0 : $i]:
% 1.02/1.19          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_B @ X0)))
% 1.02/1.19         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('demod', [status(thm)], ['87', '88'])).
% 1.02/1.19  thf('90', plain,
% 1.02/1.19      (![X30 : $i, X32 : $i]:
% 1.02/1.19         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 1.02/1.19      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.19  thf('91', plain,
% 1.02/1.19      ((![X0 : $i]:
% 1.02/1.19          (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.02/1.19           (k1_zfmisc_1 @ (k2_xboole_0 @ sk_B @ X0))))
% 1.02/1.19         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('sup-', [status(thm)], ['89', '90'])).
% 1.02/1.19  thf('92', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.02/1.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.02/1.19  thf('93', plain,
% 1.02/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('94', plain,
% 1.02/1.19      (![X30 : $i, X31 : $i]:
% 1.02/1.19         ((r1_tarski @ X30 @ X31) | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 1.02/1.19      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.19  thf('95', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.02/1.19      inference('sup-', [status(thm)], ['93', '94'])).
% 1.02/1.19  thf('96', plain,
% 1.02/1.19      (![X7 : $i, X8 : $i]:
% 1.02/1.19         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 1.02/1.19      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.02/1.19  thf('97', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 1.02/1.19      inference('sup-', [status(thm)], ['95', '96'])).
% 1.02/1.19  thf('98', plain,
% 1.02/1.19      (![X4 : $i, X5 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ X4 @ X5)
% 1.02/1.19           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.02/1.19      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.02/1.19  thf('99', plain,
% 1.02/1.19      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.02/1.19         = (k5_xboole_0 @ sk_B @ sk_B))),
% 1.02/1.19      inference('sup+', [status(thm)], ['97', '98'])).
% 1.02/1.19  thf('100', plain,
% 1.02/1.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.02/1.19         ((r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 1.02/1.19          | ~ (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15))),
% 1.02/1.19      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.02/1.19  thf('101', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         (~ (r1_tarski @ (k5_xboole_0 @ sk_B @ sk_B) @ X0)
% 1.02/1.19          | (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['99', '100'])).
% 1.02/1.19  thf('102', plain,
% 1.02/1.19      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.02/1.19         = (k5_xboole_0 @ sk_B @ sk_B))),
% 1.02/1.19      inference('sup+', [status(thm)], ['97', '98'])).
% 1.02/1.19  thf('103', plain,
% 1.02/1.19      (![X16 : $i, X17 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.02/1.19           = (k3_xboole_0 @ X16 @ X17))),
% 1.02/1.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.19  thf('104', plain,
% 1.02/1.19      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B))
% 1.02/1.19         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('sup+', [status(thm)], ['102', '103'])).
% 1.02/1.19  thf('105', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 1.02/1.19      inference('sup-', [status(thm)], ['95', '96'])).
% 1.02/1.19  thf('106', plain,
% 1.02/1.19      (((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B)) = (sk_B))),
% 1.02/1.19      inference('demod', [status(thm)], ['104', '105'])).
% 1.02/1.19  thf('107', plain,
% 1.02/1.19      (![X16 : $i, X17 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.02/1.19           = (k3_xboole_0 @ X16 @ X17))),
% 1.02/1.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.19  thf('108', plain,
% 1.02/1.19      (((k4_xboole_0 @ sk_B @ sk_B)
% 1.02/1.19         = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 1.02/1.19      inference('sup+', [status(thm)], ['106', '107'])).
% 1.02/1.19  thf('109', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.19      inference('demod', [status(thm)], ['65', '74'])).
% 1.02/1.19  thf('110', plain,
% 1.02/1.19      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 1.02/1.19      inference('demod', [status(thm)], ['108', '109'])).
% 1.02/1.19  thf('111', plain,
% 1.02/1.19      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.02/1.19         = (k5_xboole_0 @ sk_B @ sk_B))),
% 1.02/1.19      inference('sup+', [status(thm)], ['97', '98'])).
% 1.02/1.19  thf('112', plain,
% 1.02/1.19      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 1.02/1.19      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.02/1.19  thf('113', plain, ((r1_tarski @ (k5_xboole_0 @ sk_B @ sk_B) @ sk_B)),
% 1.02/1.19      inference('sup+', [status(thm)], ['111', '112'])).
% 1.02/1.19  thf('114', plain,
% 1.02/1.19      (![X7 : $i, X8 : $i]:
% 1.02/1.19         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 1.02/1.19      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.02/1.19  thf('115', plain,
% 1.02/1.19      (((k3_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_B) @ sk_B)
% 1.02/1.19         = (k5_xboole_0 @ sk_B @ sk_B))),
% 1.02/1.19      inference('sup-', [status(thm)], ['113', '114'])).
% 1.02/1.19  thf('116', plain,
% 1.02/1.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.02/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.19  thf('117', plain,
% 1.02/1.19      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B))
% 1.02/1.19         = (k5_xboole_0 @ sk_B @ sk_B))),
% 1.02/1.19      inference('demod', [status(thm)], ['115', '116'])).
% 1.02/1.19  thf('118', plain, (((k1_xboole_0) = (k5_xboole_0 @ sk_B @ sk_B))),
% 1.02/1.19      inference('sup+', [status(thm)], ['110', '117'])).
% 1.02/1.19  thf('119', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.02/1.19      inference('sup+', [status(thm)], ['66', '69'])).
% 1.02/1.19  thf('120', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 1.02/1.19      inference('demod', [status(thm)], ['101', '118', '119'])).
% 1.02/1.19  thf('121', plain,
% 1.02/1.19      (![X30 : $i, X32 : $i]:
% 1.02/1.19         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 1.02/1.19      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.19  thf('122', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         (m1_subset_1 @ sk_B @ 
% 1.02/1.19          (k1_zfmisc_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['120', '121'])).
% 1.02/1.19  thf('123', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         (m1_subset_1 @ sk_B @ 
% 1.02/1.19          (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A))))),
% 1.02/1.19      inference('sup+', [status(thm)], ['92', '122'])).
% 1.02/1.19  thf(redefinition_k4_subset_1, axiom,
% 1.02/1.19    (![A:$i,B:$i,C:$i]:
% 1.02/1.19     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.02/1.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.02/1.19       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.02/1.19  thf('124', plain,
% 1.02/1.19      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.02/1.19         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 1.02/1.19          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23))
% 1.02/1.19          | ((k4_subset_1 @ X23 @ X22 @ X24) = (k2_xboole_0 @ X22 @ X24)))),
% 1.02/1.19      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.02/1.19  thf('125', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         (((k4_subset_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B @ X1)
% 1.02/1.19            = (k2_xboole_0 @ sk_B @ X1))
% 1.02/1.19          | ~ (m1_subset_1 @ X1 @ 
% 1.02/1.19               (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))))),
% 1.02/1.19      inference('sup-', [status(thm)], ['123', '124'])).
% 1.02/1.19  thf('126', plain,
% 1.02/1.19      ((((k4_subset_1 @ (k2_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B @ 
% 1.02/1.19          (k2_tops_1 @ sk_A @ sk_B))
% 1.02/1.19          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.02/1.19         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('sup-', [status(thm)], ['91', '125'])).
% 1.02/1.19  thf('127', plain,
% 1.02/1.19      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.02/1.19         = (k5_xboole_0 @ sk_B @ sk_B))),
% 1.02/1.19      inference('sup+', [status(thm)], ['97', '98'])).
% 1.02/1.19  thf('128', plain, (((k1_xboole_0) = (k5_xboole_0 @ sk_B @ sk_B))),
% 1.02/1.19      inference('sup+', [status(thm)], ['110', '117'])).
% 1.02/1.19  thf('129', plain,
% 1.02/1.19      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 1.02/1.19      inference('demod', [status(thm)], ['127', '128'])).
% 1.02/1.19  thf('130', plain,
% 1.02/1.19      (![X11 : $i, X12 : $i]:
% 1.02/1.19         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 1.02/1.19           = (k2_xboole_0 @ X11 @ X12))),
% 1.02/1.19      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.02/1.19  thf('131', plain,
% 1.02/1.19      (((k2_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 1.02/1.19         = (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.02/1.19      inference('sup+', [status(thm)], ['129', '130'])).
% 1.02/1.19  thf('132', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.02/1.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.02/1.19  thf('133', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['57', '58'])).
% 1.02/1.19  thf('134', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.02/1.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.02/1.19  thf('135', plain,
% 1.02/1.19      (((u1_struct_0 @ sk_A) = (k2_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('demod', [status(thm)], ['131', '132', '133', '134'])).
% 1.02/1.19  thf('136', plain,
% 1.02/1.19      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.02/1.19         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('sup+', [status(thm)], ['47', '84'])).
% 1.02/1.19  thf('137', plain,
% 1.02/1.19      (![X11 : $i, X12 : $i]:
% 1.02/1.19         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 1.02/1.19           = (k2_xboole_0 @ X11 @ X12))),
% 1.02/1.19      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.02/1.19  thf('138', plain,
% 1.02/1.19      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 1.02/1.19          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.02/1.19         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('sup+', [status(thm)], ['136', '137'])).
% 1.02/1.19  thf('139', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.02/1.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.02/1.19  thf('140', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['57', '58'])).
% 1.02/1.19  thf('141', plain,
% 1.02/1.19      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.02/1.19         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('demod', [status(thm)], ['138', '139', '140'])).
% 1.02/1.19  thf('142', plain,
% 1.02/1.19      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.02/1.19          = (sk_B)))
% 1.02/1.19         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('demod', [status(thm)], ['126', '135', '141'])).
% 1.02/1.19  thf('143', plain,
% 1.02/1.19      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.02/1.19         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('sup+', [status(thm)], ['44', '142'])).
% 1.02/1.19  thf('144', plain,
% 1.02/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf(t52_pre_topc, axiom,
% 1.02/1.19    (![A:$i]:
% 1.02/1.19     ( ( l1_pre_topc @ A ) =>
% 1.02/1.19       ( ![B:$i]:
% 1.02/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.19           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.02/1.19             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.02/1.19               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.02/1.19  thf('145', plain,
% 1.02/1.19      (![X33 : $i, X34 : $i]:
% 1.02/1.19         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.02/1.19          | ~ (v2_pre_topc @ X34)
% 1.02/1.19          | ((k2_pre_topc @ X34 @ X33) != (X33))
% 1.02/1.19          | (v4_pre_topc @ X33 @ X34)
% 1.02/1.19          | ~ (l1_pre_topc @ X34))),
% 1.02/1.19      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.02/1.19  thf('146', plain,
% 1.02/1.19      ((~ (l1_pre_topc @ sk_A)
% 1.02/1.19        | (v4_pre_topc @ sk_B @ sk_A)
% 1.02/1.19        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 1.02/1.19        | ~ (v2_pre_topc @ sk_A))),
% 1.02/1.19      inference('sup-', [status(thm)], ['144', '145'])).
% 1.02/1.19  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('148', plain, ((v2_pre_topc @ sk_A)),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('149', plain,
% 1.02/1.19      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 1.02/1.19      inference('demod', [status(thm)], ['146', '147', '148'])).
% 1.02/1.19  thf('150', plain,
% 1.02/1.19      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 1.02/1.19         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('sup-', [status(thm)], ['143', '149'])).
% 1.02/1.19  thf('151', plain,
% 1.02/1.19      (((v4_pre_topc @ sk_B @ sk_A))
% 1.02/1.19         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.02/1.19      inference('simplify', [status(thm)], ['150'])).
% 1.02/1.19  thf('152', plain,
% 1.02/1.19      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.02/1.19      inference('split', [status(esa)], ['0'])).
% 1.02/1.19  thf('153', plain,
% 1.02/1.19      (~
% 1.02/1.19       (((k2_tops_1 @ sk_A @ sk_B)
% 1.02/1.19          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.19             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.02/1.19       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.02/1.19      inference('sup-', [status(thm)], ['151', '152'])).
% 1.02/1.19  thf('154', plain, ($false),
% 1.02/1.19      inference('sat_resolution*', [status(thm)], ['1', '38', '39', '153'])).
% 1.02/1.19  
% 1.02/1.19  % SZS output end Refutation
% 1.02/1.19  
% 1.02/1.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
