%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QM7HI3Lydq

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:41 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  227 ( 525 expanded)
%              Number of leaves         :   48 ( 186 expanded)
%              Depth                    :   19
%              Number of atoms          : 2001 (5436 expanded)
%              Number of equality atoms :  145 ( 391 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( ( k1_tops_1 @ X59 @ X58 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X59 ) @ X58 @ ( k2_tops_1 @ X59 @ X58 ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k4_xboole_0 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k6_subset_1 @ X36 @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k6_subset_1 @ X38 @ X40 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k6_subset_1 @ X36 @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k6_subset_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('24',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X57 @ X56 ) @ X56 )
      | ~ ( v4_pre_topc @ X56 @ X57 )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X45: $i,X47: $i] :
      ( ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( r1_tarski @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('31',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X32 @ ( k3_subset_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('32',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('34',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k6_subset_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('35',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('37',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['20','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['21'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('50',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k6_subset_1 @ X36 @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X6 @ X7 ) @ X6 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('53',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X2 @ k1_xboole_0 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('57',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k6_subset_1 @ X36 @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('58',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('59',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k3_tarski @ ( k2_tarski @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,
    ( ( r1_tarski @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X6 @ X7 ) @ X6 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('64',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('65',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k6_subset_1 @ X36 @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('66',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('69',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k3_tarski @ ( k2_tarski @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k6_subset_1 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('72',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('73',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k6_subset_1 @ X36 @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('74',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k6_subset_1 @ X9 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k6_subset_1 @ X9 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','77'])).

thf('79',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
        | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X2: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X2 @ k1_xboole_0 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X45: $i,X47: $i] :
      ( ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( r1_tarski @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r1_tarski @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X6 @ X7 ) @ X6 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('91',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('95',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k3_tarski @ ( k2_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X45: $i,X47: $i] :
      ( ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( r1_tarski @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('97',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('98',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k4_subset_1 @ X34 @ X33 @ X35 )
        = ( k2_xboole_0 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('99',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('100',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k4_subset_1 @ X34 @ X33 @ X35 )
        = ( k3_tarski @ ( k2_tarski @ X33 @ X35 ) ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ ( k3_tarski @ ( k2_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B @ X1 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X1 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k2_tarski @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ( ( k4_subset_1 @ ( k3_tarski @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['86','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X32 @ ( k3_subset_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('105',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k6_subset_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('108',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('111',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('113',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('115',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('119',plain,(
    ! [X2: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X2 @ k1_xboole_0 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('120',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k6_subset_1 @ X9 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('122',plain,
    ( ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['120','121'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('123',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('124',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k6_subset_1 @ X36 @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('125',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('126',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('127',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) )
      = X16 ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,
    ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
    = sk_B ),
    inference('sup+',[status(thm)],['122','127'])).

thf('129',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('130',plain,(
    ! [X2: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X2 @ k1_xboole_0 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['128','131'])).

thf('133',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('134',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('139',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k6_subset_1 @ X36 @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['137','140'])).

thf('142',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['132','141'])).

thf('143',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['111','142'])).

thf('144',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) )
      = X16 ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('145',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('146',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('147',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('148',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('149',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) ) ) )
      = ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['144','149'])).

thf('151',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) )
      = ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) )
      = X16 ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['143','154'])).

thf('156',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('157',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('160',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['102','157','160'])).

thf('162',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('163',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( ( k2_pre_topc @ X55 @ X54 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X55 ) @ X54 @ ( k2_tops_1 @ X55 @ X54 ) ) )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('164',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['161','166'])).

thf('168',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('169',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X50 @ X51 ) @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('170',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['167','173'])).

thf('175',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('176',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','44','45','176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QM7HI3Lydq
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:41:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.06/1.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.27  % Solved by: fo/fo7.sh
% 1.06/1.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.27  % done 3157 iterations in 0.825s
% 1.06/1.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.27  % SZS output start Refutation
% 1.06/1.27  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.06/1.27  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.27  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.27  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.06/1.27  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.06/1.27  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.27  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.06/1.27  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.06/1.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.27  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.27  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.06/1.27  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.27  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.06/1.27  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.06/1.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.27  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.27  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.06/1.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.27  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.06/1.27  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.27  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.06/1.27  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.06/1.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.27  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.06/1.27  thf(t77_tops_1, conjecture,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27           ( ( v4_pre_topc @ B @ A ) <=>
% 1.06/1.27             ( ( k2_tops_1 @ A @ B ) =
% 1.06/1.27               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.06/1.27  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.27    (~( ![A:$i]:
% 1.06/1.27        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.27          ( ![B:$i]:
% 1.06/1.27            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27              ( ( v4_pre_topc @ B @ A ) <=>
% 1.06/1.27                ( ( k2_tops_1 @ A @ B ) =
% 1.06/1.27                  ( k7_subset_1 @
% 1.06/1.27                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.06/1.27    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.06/1.27  thf('0', plain,
% 1.06/1.27      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27              (k1_tops_1 @ sk_A @ sk_B)))
% 1.06/1.27        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('1', plain,
% 1.06/1.27      (~
% 1.06/1.27       (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.06/1.27       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.27      inference('split', [status(esa)], ['0'])).
% 1.06/1.27  thf('2', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(t74_tops_1, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( l1_pre_topc @ A ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27           ( ( k1_tops_1 @ A @ B ) =
% 1.06/1.27             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.06/1.27  thf('3', plain,
% 1.06/1.27      (![X58 : $i, X59 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 1.06/1.27          | ((k1_tops_1 @ X59 @ X58)
% 1.06/1.27              = (k7_subset_1 @ (u1_struct_0 @ X59) @ X58 @ 
% 1.06/1.27                 (k2_tops_1 @ X59 @ X58)))
% 1.06/1.27          | ~ (l1_pre_topc @ X59))),
% 1.06/1.27      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.06/1.27  thf('4', plain,
% 1.06/1.27      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.27        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.27            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['2', '3'])).
% 1.06/1.27  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('6', plain,
% 1.06/1.27      (((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.27         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.27      inference('demod', [status(thm)], ['4', '5'])).
% 1.06/1.27  thf('7', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(redefinition_k7_subset_1, axiom,
% 1.06/1.27    (![A:$i,B:$i,C:$i]:
% 1.06/1.27     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.27       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.06/1.27  thf('8', plain,
% 1.06/1.27      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 1.06/1.27          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k4_xboole_0 @ X38 @ X40)))),
% 1.06/1.27      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.06/1.27  thf(redefinition_k6_subset_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.06/1.27  thf('9', plain,
% 1.06/1.27      (![X36 : $i, X37 : $i]:
% 1.06/1.27         ((k6_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.27  thf('10', plain,
% 1.06/1.27      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 1.06/1.27          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k6_subset_1 @ X38 @ X40)))),
% 1.06/1.27      inference('demod', [status(thm)], ['8', '9'])).
% 1.06/1.27  thf('11', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.27           = (k6_subset_1 @ sk_B @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['7', '10'])).
% 1.06/1.27  thf('12', plain,
% 1.06/1.27      (((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.27         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.27      inference('demod', [status(thm)], ['6', '11'])).
% 1.06/1.27  thf(dt_k6_subset_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.06/1.27  thf('13', plain,
% 1.06/1.27      (![X29 : $i, X30 : $i]:
% 1.06/1.27         (m1_subset_1 @ (k6_subset_1 @ X29 @ X30) @ (k1_zfmisc_1 @ X29))),
% 1.06/1.27      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.06/1.27  thf(d5_subset_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.27       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.06/1.27  thf('14', plain,
% 1.06/1.27      (![X25 : $i, X26 : $i]:
% 1.06/1.27         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 1.06/1.27          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 1.06/1.27      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.06/1.27  thf('15', plain,
% 1.06/1.27      (![X36 : $i, X37 : $i]:
% 1.06/1.27         ((k6_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.27  thf('16', plain,
% 1.06/1.27      (![X25 : $i, X26 : $i]:
% 1.06/1.27         (((k3_subset_1 @ X25 @ X26) = (k6_subset_1 @ X25 @ X26))
% 1.06/1.27          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 1.06/1.27      inference('demod', [status(thm)], ['14', '15'])).
% 1.06/1.27  thf('17', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 1.06/1.27           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['13', '16'])).
% 1.06/1.27  thf('18', plain,
% 1.06/1.27      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.06/1.27         = (k6_subset_1 @ sk_B @ 
% 1.06/1.27            (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.06/1.27      inference('sup+', [status(thm)], ['12', '17'])).
% 1.06/1.27  thf('19', plain,
% 1.06/1.27      (((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.27         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.27      inference('demod', [status(thm)], ['6', '11'])).
% 1.06/1.27  thf('20', plain,
% 1.06/1.27      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.06/1.27         = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.27      inference('demod', [status(thm)], ['18', '19'])).
% 1.06/1.27  thf('21', plain,
% 1.06/1.27      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27             (k1_tops_1 @ sk_A @ sk_B)))
% 1.06/1.27        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('22', plain,
% 1.06/1.27      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.27      inference('split', [status(esa)], ['21'])).
% 1.06/1.27  thf('23', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(t69_tops_1, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( l1_pre_topc @ A ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27           ( ( v4_pre_topc @ B @ A ) =>
% 1.06/1.27             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.06/1.27  thf('24', plain,
% 1.06/1.27      (![X56 : $i, X57 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 1.06/1.27          | (r1_tarski @ (k2_tops_1 @ X57 @ X56) @ X56)
% 1.06/1.27          | ~ (v4_pre_topc @ X56 @ X57)
% 1.06/1.27          | ~ (l1_pre_topc @ X57))),
% 1.06/1.27      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.06/1.27  thf('25', plain,
% 1.06/1.27      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.27        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.06/1.27        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.06/1.27      inference('sup-', [status(thm)], ['23', '24'])).
% 1.06/1.27  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('27', plain,
% 1.06/1.27      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.06/1.27        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.06/1.27      inference('demod', [status(thm)], ['25', '26'])).
% 1.06/1.27  thf('28', plain,
% 1.06/1.27      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.06/1.27         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['22', '27'])).
% 1.06/1.27  thf(t3_subset, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.27  thf('29', plain,
% 1.06/1.27      (![X45 : $i, X47 : $i]:
% 1.06/1.27         ((m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X47)) | ~ (r1_tarski @ X45 @ X47))),
% 1.06/1.27      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.27  thf('30', plain,
% 1.06/1.27      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.06/1.27         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['28', '29'])).
% 1.06/1.27  thf(involutiveness_k3_subset_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.27       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.06/1.27  thf('31', plain,
% 1.06/1.27      (![X31 : $i, X32 : $i]:
% 1.06/1.27         (((k3_subset_1 @ X32 @ (k3_subset_1 @ X32 @ X31)) = (X31))
% 1.06/1.27          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 1.06/1.27      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.06/1.27  thf('32', plain,
% 1.06/1.27      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.27          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.27         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['30', '31'])).
% 1.06/1.27  thf('33', plain,
% 1.06/1.27      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.06/1.27         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['28', '29'])).
% 1.06/1.27  thf('34', plain,
% 1.06/1.27      (![X25 : $i, X26 : $i]:
% 1.06/1.27         (((k3_subset_1 @ X25 @ X26) = (k6_subset_1 @ X25 @ X26))
% 1.06/1.27          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 1.06/1.27      inference('demod', [status(thm)], ['14', '15'])).
% 1.06/1.27  thf('35', plain,
% 1.06/1.27      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.27          = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.06/1.27         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['33', '34'])).
% 1.06/1.27  thf('36', plain,
% 1.06/1.27      (((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.27         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.27      inference('demod', [status(thm)], ['6', '11'])).
% 1.06/1.27  thf('37', plain,
% 1.06/1.27      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.27          = (k1_tops_1 @ sk_A @ sk_B)))
% 1.06/1.27         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.27      inference('demod', [status(thm)], ['35', '36'])).
% 1.06/1.27  thf('38', plain,
% 1.06/1.27      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.06/1.27          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.27         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.27      inference('demod', [status(thm)], ['32', '37'])).
% 1.06/1.27  thf('39', plain,
% 1.06/1.27      ((((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.06/1.27          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.27         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.27      inference('sup+', [status(thm)], ['20', '38'])).
% 1.06/1.27  thf('40', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.27           = (k6_subset_1 @ sk_B @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['7', '10'])).
% 1.06/1.27  thf('41', plain,
% 1.06/1.27      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27              (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.27         <= (~
% 1.06/1.27             (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('split', [status(esa)], ['0'])).
% 1.06/1.27  thf('42', plain,
% 1.06/1.27      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.27         <= (~
% 1.06/1.27             (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['40', '41'])).
% 1.06/1.27  thf('43', plain,
% 1.06/1.27      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.06/1.27         <= (~
% 1.06/1.27             (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.06/1.27             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['39', '42'])).
% 1.06/1.27  thf('44', plain,
% 1.06/1.27      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.06/1.27       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.27      inference('simplify', [status(thm)], ['43'])).
% 1.06/1.27  thf('45', plain,
% 1.06/1.27      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.06/1.27       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.27      inference('split', [status(esa)], ['21'])).
% 1.06/1.27  thf('46', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.27           = (k6_subset_1 @ sk_B @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['7', '10'])).
% 1.06/1.27  thf('47', plain,
% 1.06/1.27      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27             (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.27         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('split', [status(esa)], ['21'])).
% 1.06/1.27  thf('48', plain,
% 1.06/1.27      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.27         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('sup+', [status(thm)], ['46', '47'])).
% 1.06/1.27  thf(t36_xboole_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.06/1.27  thf('49', plain,
% 1.06/1.27      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.06/1.27      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.06/1.27  thf('50', plain,
% 1.06/1.27      (![X36 : $i, X37 : $i]:
% 1.06/1.27         ((k6_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.27  thf('51', plain,
% 1.06/1.27      (![X6 : $i, X7 : $i]: (r1_tarski @ (k6_subset_1 @ X6 @ X7) @ X6)),
% 1.06/1.27      inference('demod', [status(thm)], ['49', '50'])).
% 1.06/1.27  thf('52', plain,
% 1.06/1.27      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.06/1.27         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('sup+', [status(thm)], ['48', '51'])).
% 1.06/1.27  thf(t1_boole, axiom,
% 1.06/1.27    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.06/1.27  thf('53', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 1.06/1.27      inference('cnf', [status(esa)], [t1_boole])).
% 1.06/1.27  thf(l51_zfmisc_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.06/1.27  thf('54', plain,
% 1.06/1.27      (![X22 : $i, X23 : $i]:
% 1.06/1.27         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 1.06/1.27      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.06/1.27  thf('55', plain,
% 1.06/1.27      (![X2 : $i]: ((k3_tarski @ (k2_tarski @ X2 @ k1_xboole_0)) = (X2))),
% 1.06/1.27      inference('demod', [status(thm)], ['53', '54'])).
% 1.06/1.27  thf(t43_xboole_1, axiom,
% 1.06/1.27    (![A:$i,B:$i,C:$i]:
% 1.06/1.27     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.06/1.27       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.06/1.27  thf('56', plain,
% 1.06/1.27      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.06/1.27         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.06/1.27          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.06/1.27      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.06/1.27  thf('57', plain,
% 1.06/1.27      (![X36 : $i, X37 : $i]:
% 1.06/1.27         ((k6_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.27  thf('58', plain,
% 1.06/1.27      (![X22 : $i, X23 : $i]:
% 1.06/1.27         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 1.06/1.27      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.06/1.27  thf('59', plain,
% 1.06/1.27      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.06/1.27         ((r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X12)
% 1.06/1.27          | ~ (r1_tarski @ X10 @ (k3_tarski @ (k2_tarski @ X11 @ X12))))),
% 1.06/1.27      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.06/1.27  thf('60', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         (~ (r1_tarski @ X1 @ X0)
% 1.06/1.27          | (r1_tarski @ (k6_subset_1 @ X1 @ X0) @ k1_xboole_0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['55', '59'])).
% 1.06/1.27  thf('61', plain,
% 1.06/1.27      (((r1_tarski @ (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 1.06/1.27         k1_xboole_0))
% 1.06/1.27         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['52', '60'])).
% 1.06/1.27  thf('62', plain,
% 1.06/1.27      (![X6 : $i, X7 : $i]: (r1_tarski @ (k6_subset_1 @ X6 @ X7) @ X6)),
% 1.06/1.27      inference('demod', [status(thm)], ['49', '50'])).
% 1.06/1.27  thf(t44_xboole_1, axiom,
% 1.06/1.27    (![A:$i,B:$i,C:$i]:
% 1.06/1.27     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.06/1.27       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.06/1.27  thf('63', plain,
% 1.06/1.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.06/1.27         ((r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 1.06/1.27          | ~ (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15))),
% 1.06/1.27      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.06/1.27  thf('64', plain,
% 1.06/1.27      (![X22 : $i, X23 : $i]:
% 1.06/1.27         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 1.06/1.27      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.06/1.27  thf('65', plain,
% 1.06/1.27      (![X36 : $i, X37 : $i]:
% 1.06/1.27         ((k6_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.27  thf('66', plain,
% 1.06/1.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.06/1.27         ((r1_tarski @ X13 @ (k3_tarski @ (k2_tarski @ X14 @ X15)))
% 1.06/1.27          | ~ (r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15))),
% 1.06/1.27      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.06/1.27  thf('67', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['62', '66'])).
% 1.06/1.27  thf(commutativity_k2_tarski, axiom,
% 1.06/1.27    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.06/1.27  thf('68', plain,
% 1.06/1.27      (![X20 : $i, X21 : $i]:
% 1.06/1.27         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 1.06/1.27      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.06/1.27  thf('69', plain,
% 1.06/1.27      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.06/1.27         ((r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X12)
% 1.06/1.27          | ~ (r1_tarski @ X10 @ (k3_tarski @ (k2_tarski @ X11 @ X12))))),
% 1.06/1.27      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.06/1.27  thf('70', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.27         (~ (r1_tarski @ X2 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))
% 1.06/1.27          | (r1_tarski @ (k6_subset_1 @ X2 @ X0) @ X1))),
% 1.06/1.27      inference('sup-', [status(thm)], ['68', '69'])).
% 1.06/1.27  thf('71', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X0) @ X1)),
% 1.06/1.27      inference('sup-', [status(thm)], ['67', '70'])).
% 1.06/1.27  thf(t38_xboole_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 1.06/1.27       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.06/1.27  thf('72', plain,
% 1.06/1.27      (![X8 : $i, X9 : $i]:
% 1.06/1.27         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 1.06/1.27      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.06/1.27  thf('73', plain,
% 1.06/1.27      (![X36 : $i, X37 : $i]:
% 1.06/1.27         ((k6_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.27  thf('74', plain,
% 1.06/1.27      (![X8 : $i, X9 : $i]:
% 1.06/1.27         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k6_subset_1 @ X9 @ X8)))),
% 1.06/1.27      inference('demod', [status(thm)], ['72', '73'])).
% 1.06/1.27  thf('75', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['71', '74'])).
% 1.06/1.27  thf('76', plain,
% 1.06/1.27      (![X8 : $i, X9 : $i]:
% 1.06/1.27         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k6_subset_1 @ X9 @ X8)))),
% 1.06/1.27      inference('demod', [status(thm)], ['72', '73'])).
% 1.06/1.27  thf('77', plain,
% 1.06/1.27      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['75', '76'])).
% 1.06/1.27  thf('78', plain,
% 1.06/1.27      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.06/1.27         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['61', '77'])).
% 1.06/1.27  thf('79', plain,
% 1.06/1.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.06/1.27         ((r1_tarski @ X13 @ (k3_tarski @ (k2_tarski @ X14 @ X15)))
% 1.06/1.27          | ~ (r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15))),
% 1.06/1.27      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.06/1.27  thf('80', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          (~ (r1_tarski @ k1_xboole_0 @ X0)
% 1.06/1.27           | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.27              (k3_tarski @ (k2_tarski @ sk_B @ X0)))))
% 1.06/1.27         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['78', '79'])).
% 1.06/1.27  thf('81', plain,
% 1.06/1.27      (![X2 : $i]: ((k3_tarski @ (k2_tarski @ X2 @ k1_xboole_0)) = (X2))),
% 1.06/1.27      inference('demod', [status(thm)], ['53', '54'])).
% 1.06/1.27  thf('82', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['62', '66'])).
% 1.06/1.27  thf('83', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.06/1.27      inference('sup+', [status(thm)], ['81', '82'])).
% 1.06/1.27  thf('84', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.27           (k3_tarski @ (k2_tarski @ sk_B @ X0))))
% 1.06/1.27         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('demod', [status(thm)], ['80', '83'])).
% 1.06/1.27  thf('85', plain,
% 1.06/1.27      (![X45 : $i, X47 : $i]:
% 1.06/1.27         ((m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X47)) | ~ (r1_tarski @ X45 @ X47))),
% 1.06/1.27      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.27  thf('86', plain,
% 1.06/1.27      ((![X0 : $i]:
% 1.06/1.27          (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.27           (k1_zfmisc_1 @ (k3_tarski @ (k2_tarski @ sk_B @ X0)))))
% 1.06/1.27         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['84', '85'])).
% 1.06/1.27  thf('87', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('88', plain,
% 1.06/1.27      (![X45 : $i, X46 : $i]:
% 1.06/1.27         ((r1_tarski @ X45 @ X46) | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46)))),
% 1.06/1.27      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.27  thf('89', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.06/1.27      inference('sup-', [status(thm)], ['87', '88'])).
% 1.06/1.27  thf('90', plain,
% 1.06/1.27      (![X6 : $i, X7 : $i]: (r1_tarski @ (k6_subset_1 @ X6 @ X7) @ X6)),
% 1.06/1.27      inference('demod', [status(thm)], ['49', '50'])).
% 1.06/1.27  thf(t1_xboole_1, axiom,
% 1.06/1.27    (![A:$i,B:$i,C:$i]:
% 1.06/1.27     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.06/1.27       ( r1_tarski @ A @ C ) ))).
% 1.06/1.27  thf('91', plain,
% 1.06/1.27      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.27         (~ (r1_tarski @ X3 @ X4)
% 1.06/1.27          | ~ (r1_tarski @ X4 @ X5)
% 1.06/1.27          | (r1_tarski @ X3 @ X5))),
% 1.06/1.27      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.06/1.27  thf('92', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.27         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 1.06/1.27      inference('sup-', [status(thm)], ['90', '91'])).
% 1.06/1.27  thf('93', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (r1_tarski @ (k6_subset_1 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 1.06/1.27      inference('sup-', [status(thm)], ['89', '92'])).
% 1.06/1.27  thf('94', plain,
% 1.06/1.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.06/1.27         ((r1_tarski @ X13 @ (k3_tarski @ (k2_tarski @ X14 @ X15)))
% 1.06/1.27          | ~ (r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15))),
% 1.06/1.27      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.06/1.27  thf('95', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (r1_tarski @ sk_B @ 
% 1.06/1.27          (k3_tarski @ (k2_tarski @ X0 @ (u1_struct_0 @ sk_A))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['93', '94'])).
% 1.06/1.27  thf('96', plain,
% 1.06/1.27      (![X45 : $i, X47 : $i]:
% 1.06/1.27         ((m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X47)) | ~ (r1_tarski @ X45 @ X47))),
% 1.06/1.27      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.27  thf('97', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (m1_subset_1 @ sk_B @ 
% 1.06/1.27          (k1_zfmisc_1 @ (k3_tarski @ (k2_tarski @ X0 @ (u1_struct_0 @ sk_A)))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['95', '96'])).
% 1.06/1.27  thf(redefinition_k4_subset_1, axiom,
% 1.06/1.27    (![A:$i,B:$i,C:$i]:
% 1.06/1.27     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.06/1.27         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.06/1.27       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.06/1.27  thf('98', plain,
% 1.06/1.27      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 1.06/1.27          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34))
% 1.06/1.27          | ((k4_subset_1 @ X34 @ X33 @ X35) = (k2_xboole_0 @ X33 @ X35)))),
% 1.06/1.27      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.06/1.27  thf('99', plain,
% 1.06/1.27      (![X22 : $i, X23 : $i]:
% 1.06/1.27         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 1.06/1.27      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.06/1.27  thf('100', plain,
% 1.06/1.27      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 1.06/1.27          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34))
% 1.06/1.27          | ((k4_subset_1 @ X34 @ X33 @ X35)
% 1.06/1.27              = (k3_tarski @ (k2_tarski @ X33 @ X35))))),
% 1.06/1.27      inference('demod', [status(thm)], ['98', '99'])).
% 1.06/1.27  thf('101', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         (((k4_subset_1 @ 
% 1.06/1.27            (k3_tarski @ (k2_tarski @ X0 @ (u1_struct_0 @ sk_A))) @ sk_B @ X1)
% 1.06/1.27            = (k3_tarski @ (k2_tarski @ sk_B @ X1)))
% 1.06/1.27          | ~ (m1_subset_1 @ X1 @ 
% 1.06/1.27               (k1_zfmisc_1 @ 
% 1.06/1.27                (k3_tarski @ (k2_tarski @ X0 @ (u1_struct_0 @ sk_A))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['97', '100'])).
% 1.06/1.27  thf('102', plain,
% 1.06/1.27      ((((k4_subset_1 @ 
% 1.06/1.27          (k3_tarski @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_B @ 
% 1.06/1.27          (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.27          = (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 1.06/1.27         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['86', '101'])).
% 1.06/1.27  thf('103', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('104', plain,
% 1.06/1.27      (![X31 : $i, X32 : $i]:
% 1.06/1.27         (((k3_subset_1 @ X32 @ (k3_subset_1 @ X32 @ X31)) = (X31))
% 1.06/1.27          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 1.06/1.27      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.06/1.27  thf('105', plain,
% 1.06/1.27      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.06/1.27      inference('sup-', [status(thm)], ['103', '104'])).
% 1.06/1.27  thf('106', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('107', plain,
% 1.06/1.27      (![X25 : $i, X26 : $i]:
% 1.06/1.27         (((k3_subset_1 @ X25 @ X26) = (k6_subset_1 @ X25 @ X26))
% 1.06/1.27          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 1.06/1.27      inference('demod', [status(thm)], ['14', '15'])).
% 1.06/1.27  thf('108', plain,
% 1.06/1.27      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.06/1.27         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.06/1.27      inference('sup-', [status(thm)], ['106', '107'])).
% 1.06/1.27  thf('109', plain,
% 1.06/1.27      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.06/1.27      inference('demod', [status(thm)], ['105', '108'])).
% 1.06/1.27  thf('110', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 1.06/1.27           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['13', '16'])).
% 1.06/1.27  thf('111', plain,
% 1.06/1.27      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.06/1.27      inference('demod', [status(thm)], ['109', '110'])).
% 1.06/1.27  thf('112', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['62', '66'])).
% 1.06/1.27  thf('113', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.06/1.27      inference('sup-', [status(thm)], ['87', '88'])).
% 1.06/1.27  thf('114', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         (~ (r1_tarski @ X1 @ X0)
% 1.06/1.27          | (r1_tarski @ (k6_subset_1 @ X1 @ X0) @ k1_xboole_0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['55', '59'])).
% 1.06/1.27  thf('115', plain,
% 1.06/1.27      ((r1_tarski @ (k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ k1_xboole_0)),
% 1.06/1.27      inference('sup-', [status(thm)], ['113', '114'])).
% 1.06/1.27  thf('116', plain,
% 1.06/1.27      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.27         (~ (r1_tarski @ X3 @ X4)
% 1.06/1.27          | ~ (r1_tarski @ X4 @ X5)
% 1.06/1.27          | (r1_tarski @ X3 @ X5))),
% 1.06/1.27      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.06/1.27  thf('117', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         ((r1_tarski @ (k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)
% 1.06/1.27          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['115', '116'])).
% 1.06/1.27  thf('118', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (r1_tarski @ (k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 1.06/1.27          (k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['112', '117'])).
% 1.06/1.27  thf('119', plain,
% 1.06/1.27      (![X2 : $i]: ((k3_tarski @ (k2_tarski @ X2 @ k1_xboole_0)) = (X2))),
% 1.06/1.27      inference('demod', [status(thm)], ['53', '54'])).
% 1.06/1.27  thf('120', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (r1_tarski @ (k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 1.06/1.27      inference('demod', [status(thm)], ['118', '119'])).
% 1.06/1.27  thf('121', plain,
% 1.06/1.27      (![X8 : $i, X9 : $i]:
% 1.06/1.27         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k6_subset_1 @ X9 @ X8)))),
% 1.06/1.27      inference('demod', [status(thm)], ['72', '73'])).
% 1.06/1.27  thf('122', plain,
% 1.06/1.27      (((k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['120', '121'])).
% 1.06/1.27  thf(t51_xboole_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.06/1.27       ( A ) ))).
% 1.06/1.27  thf('123', plain,
% 1.06/1.27      (![X16 : $i, X17 : $i]:
% 1.06/1.27         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 1.06/1.27           = (X16))),
% 1.06/1.27      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.06/1.27  thf('124', plain,
% 1.06/1.27      (![X36 : $i, X37 : $i]:
% 1.06/1.27         ((k6_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.27  thf('125', plain,
% 1.06/1.27      (![X22 : $i, X23 : $i]:
% 1.06/1.27         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 1.06/1.27      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.06/1.27  thf('126', plain,
% 1.06/1.27      (![X20 : $i, X21 : $i]:
% 1.06/1.27         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 1.06/1.27      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.06/1.27  thf('127', plain,
% 1.06/1.27      (![X16 : $i, X17 : $i]:
% 1.06/1.27         ((k3_tarski @ 
% 1.06/1.27           (k2_tarski @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17)))
% 1.06/1.27           = (X16))),
% 1.06/1.27      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 1.06/1.27  thf('128', plain,
% 1.06/1.27      (((k3_tarski @ 
% 1.06/1.27         (k2_tarski @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))
% 1.06/1.27         = (sk_B))),
% 1.06/1.27      inference('sup+', [status(thm)], ['122', '127'])).
% 1.06/1.27  thf('129', plain,
% 1.06/1.27      (![X20 : $i, X21 : $i]:
% 1.06/1.27         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 1.06/1.27      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.06/1.27  thf('130', plain,
% 1.06/1.27      (![X2 : $i]: ((k3_tarski @ (k2_tarski @ X2 @ k1_xboole_0)) = (X2))),
% 1.06/1.27      inference('demod', [status(thm)], ['53', '54'])).
% 1.06/1.27  thf('131', plain,
% 1.06/1.27      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 1.06/1.27      inference('sup+', [status(thm)], ['129', '130'])).
% 1.06/1.27  thf('132', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 1.06/1.27      inference('demod', [status(thm)], ['128', '131'])).
% 1.06/1.27  thf('133', plain,
% 1.06/1.27      (![X20 : $i, X21 : $i]:
% 1.06/1.27         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 1.06/1.27      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.06/1.27  thf(t12_setfam_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.06/1.27  thf('134', plain,
% 1.06/1.27      (![X43 : $i, X44 : $i]:
% 1.06/1.27         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 1.06/1.27      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.06/1.27  thf('135', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.27      inference('sup+', [status(thm)], ['133', '134'])).
% 1.06/1.27  thf('136', plain,
% 1.06/1.27      (![X43 : $i, X44 : $i]:
% 1.06/1.27         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 1.06/1.27      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.06/1.27  thf('137', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.27      inference('sup+', [status(thm)], ['135', '136'])).
% 1.06/1.27  thf(t100_xboole_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.06/1.27  thf('138', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         ((k4_xboole_0 @ X0 @ X1)
% 1.06/1.27           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.06/1.27      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.06/1.27  thf('139', plain,
% 1.06/1.27      (![X36 : $i, X37 : $i]:
% 1.06/1.27         ((k6_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.27  thf('140', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         ((k6_subset_1 @ X0 @ X1)
% 1.06/1.27           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.06/1.27      inference('demod', [status(thm)], ['138', '139'])).
% 1.06/1.27  thf('141', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         ((k6_subset_1 @ X0 @ X1)
% 1.06/1.27           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.06/1.27      inference('sup+', [status(thm)], ['137', '140'])).
% 1.06/1.27  thf('142', plain,
% 1.06/1.27      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.06/1.27         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.06/1.27      inference('sup+', [status(thm)], ['132', '141'])).
% 1.06/1.27  thf('143', plain,
% 1.06/1.27      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.06/1.27      inference('demod', [status(thm)], ['111', '142'])).
% 1.06/1.27  thf('144', plain,
% 1.06/1.27      (![X16 : $i, X17 : $i]:
% 1.06/1.27         ((k3_tarski @ 
% 1.06/1.27           (k2_tarski @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17)))
% 1.06/1.27           = (X16))),
% 1.06/1.27      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 1.06/1.27  thf(t6_xboole_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.06/1.27  thf('145', plain,
% 1.06/1.27      (![X18 : $i, X19 : $i]:
% 1.06/1.27         ((k2_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19))
% 1.06/1.27           = (k2_xboole_0 @ X18 @ X19))),
% 1.06/1.27      inference('cnf', [status(esa)], [t6_xboole_1])).
% 1.06/1.27  thf('146', plain,
% 1.06/1.27      (![X22 : $i, X23 : $i]:
% 1.06/1.27         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 1.06/1.27      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.06/1.27  thf('147', plain,
% 1.06/1.27      (![X22 : $i, X23 : $i]:
% 1.06/1.27         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 1.06/1.27      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.06/1.27  thf('148', plain,
% 1.06/1.27      (![X22 : $i, X23 : $i]:
% 1.06/1.27         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 1.06/1.27      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.06/1.27  thf('149', plain,
% 1.06/1.27      (![X18 : $i, X19 : $i]:
% 1.06/1.27         ((k3_tarski @ 
% 1.06/1.27           (k2_tarski @ X18 @ (k3_tarski @ (k2_tarski @ X18 @ X19))))
% 1.06/1.27           = (k3_tarski @ (k2_tarski @ X18 @ X19)))),
% 1.06/1.27      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 1.06/1.27  thf('150', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         ((k3_tarski @ (k2_tarski @ (k6_subset_1 @ X0 @ X1) @ X0))
% 1.06/1.27           = (k3_tarski @ 
% 1.06/1.27              (k2_tarski @ (k6_subset_1 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))))),
% 1.06/1.27      inference('sup+', [status(thm)], ['144', '149'])).
% 1.06/1.27  thf('151', plain,
% 1.06/1.27      (![X20 : $i, X21 : $i]:
% 1.06/1.27         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 1.06/1.27      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.06/1.27  thf('152', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         ((k3_tarski @ (k2_tarski @ X0 @ (k6_subset_1 @ X0 @ X1)))
% 1.06/1.27           = (k3_tarski @ 
% 1.06/1.27              (k2_tarski @ (k6_subset_1 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))))),
% 1.06/1.27      inference('demod', [status(thm)], ['150', '151'])).
% 1.06/1.27  thf('153', plain,
% 1.06/1.27      (![X16 : $i, X17 : $i]:
% 1.06/1.27         ((k3_tarski @ 
% 1.06/1.27           (k2_tarski @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17)))
% 1.06/1.27           = (X16))),
% 1.06/1.27      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 1.06/1.27  thf('154', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         ((k3_tarski @ (k2_tarski @ X1 @ (k6_subset_1 @ X1 @ X0))) = (X1))),
% 1.06/1.27      inference('sup+', [status(thm)], ['152', '153'])).
% 1.06/1.27  thf('155', plain,
% 1.06/1.27      (((k3_tarski @ (k2_tarski @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.06/1.27         = (u1_struct_0 @ sk_A))),
% 1.06/1.27      inference('sup+', [status(thm)], ['143', '154'])).
% 1.06/1.27  thf('156', plain,
% 1.06/1.27      (![X20 : $i, X21 : $i]:
% 1.06/1.27         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 1.06/1.27      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.06/1.27  thf('157', plain,
% 1.06/1.27      (((k3_tarski @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A)))
% 1.06/1.27         = (u1_struct_0 @ sk_A))),
% 1.06/1.27      inference('demod', [status(thm)], ['155', '156'])).
% 1.06/1.27  thf('158', plain,
% 1.06/1.27      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.27         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('sup+', [status(thm)], ['46', '47'])).
% 1.06/1.27  thf('159', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         ((k3_tarski @ (k2_tarski @ X1 @ (k6_subset_1 @ X1 @ X0))) = (X1))),
% 1.06/1.27      inference('sup+', [status(thm)], ['152', '153'])).
% 1.06/1.27  thf('160', plain,
% 1.06/1.27      ((((k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 1.06/1.27         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('sup+', [status(thm)], ['158', '159'])).
% 1.06/1.27  thf('161', plain,
% 1.06/1.27      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.27          = (sk_B)))
% 1.06/1.27         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('demod', [status(thm)], ['102', '157', '160'])).
% 1.06/1.27  thf('162', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(t65_tops_1, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( l1_pre_topc @ A ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27           ( ( k2_pre_topc @ A @ B ) =
% 1.06/1.27             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.06/1.27  thf('163', plain,
% 1.06/1.27      (![X54 : $i, X55 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 1.06/1.27          | ((k2_pre_topc @ X55 @ X54)
% 1.06/1.27              = (k4_subset_1 @ (u1_struct_0 @ X55) @ X54 @ 
% 1.06/1.27                 (k2_tops_1 @ X55 @ X54)))
% 1.06/1.27          | ~ (l1_pre_topc @ X55))),
% 1.06/1.27      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.06/1.27  thf('164', plain,
% 1.06/1.27      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.27        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.06/1.27            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['162', '163'])).
% 1.06/1.27  thf('165', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('166', plain,
% 1.06/1.27      (((k2_pre_topc @ sk_A @ sk_B)
% 1.06/1.27         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.27      inference('demod', [status(thm)], ['164', '165'])).
% 1.06/1.27  thf('167', plain,
% 1.06/1.27      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.06/1.27         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('sup+', [status(thm)], ['161', '166'])).
% 1.06/1.27  thf('168', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(fc1_tops_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.06/1.27         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.27       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.06/1.27  thf('169', plain,
% 1.06/1.27      (![X50 : $i, X51 : $i]:
% 1.06/1.27         (~ (l1_pre_topc @ X50)
% 1.06/1.27          | ~ (v2_pre_topc @ X50)
% 1.06/1.27          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 1.06/1.27          | (v4_pre_topc @ (k2_pre_topc @ X50 @ X51) @ X50))),
% 1.06/1.27      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.06/1.27  thf('170', plain,
% 1.06/1.27      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.06/1.27        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.27        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.27      inference('sup-', [status(thm)], ['168', '169'])).
% 1.06/1.27  thf('171', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('172', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('173', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.06/1.27      inference('demod', [status(thm)], ['170', '171', '172'])).
% 1.06/1.27  thf('174', plain,
% 1.06/1.27      (((v4_pre_topc @ sk_B @ sk_A))
% 1.06/1.27         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.27      inference('sup+', [status(thm)], ['167', '173'])).
% 1.06/1.27  thf('175', plain,
% 1.06/1.27      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.27      inference('split', [status(esa)], ['0'])).
% 1.06/1.27  thf('176', plain,
% 1.06/1.27      (~
% 1.06/1.27       (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.27          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.06/1.27       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.27      inference('sup-', [status(thm)], ['174', '175'])).
% 1.06/1.27  thf('177', plain, ($false),
% 1.06/1.27      inference('sat_resolution*', [status(thm)], ['1', '44', '45', '176'])).
% 1.06/1.27  
% 1.06/1.27  % SZS output end Refutation
% 1.06/1.27  
% 1.06/1.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
