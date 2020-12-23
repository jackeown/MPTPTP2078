%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jpIGWgxNxn

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:26 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 276 expanded)
%              Number of leaves         :   43 (  97 expanded)
%              Depth                    :   13
%              Number of atoms          : 1378 (3181 expanded)
%              Number of equality atoms :   98 ( 205 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( v3_pre_topc @ X50 @ X51 )
      | ~ ( r1_tarski @ X50 @ X52 )
      | ( r1_tarski @ X50 @ ( k1_tops_1 @ X51 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
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
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( ( k1_tops_1 @ X58 @ X57 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X58 ) @ X57 @ ( k2_tops_1 @ X58 @ X57 ) ) )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k7_subset_1 @ X37 @ X36 @ X38 )
        = ( k4_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k2_tops_1 @ X49 @ X48 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X49 ) @ ( k2_pre_topc @ X49 @ X48 ) @ ( k1_tops_1 @ X49 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( l1_pre_topc @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X44 @ X45 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X29 @ X28 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('50',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k2_pre_topc @ X56 @ X55 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 @ ( k2_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k7_subset_1 @ X37 @ X36 @ X38 )
        = ( k4_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('62',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('66',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('67',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('68',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('69',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) ) )
      = ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) ) @ X21 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X1 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['65','71'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('73',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('74',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('75',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('76',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('79',plain,(
    ! [X41: $i,X43: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( r1_tarski @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('81',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('83',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('84',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('85',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('86',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('89',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('90',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('91',plain,(
    ! [X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('95',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('97',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['72','77','95','100'])).

thf('102',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['58','101'])).

thf('103',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('104',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('106',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X46 @ X47 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('107',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['104','110'])).

thf('112',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','38','39','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jpIGWgxNxn
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:34:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.97/2.22  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.97/2.22  % Solved by: fo/fo7.sh
% 1.97/2.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.97/2.22  % done 4851 iterations in 1.757s
% 1.97/2.22  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.97/2.22  % SZS output start Refutation
% 1.97/2.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.97/2.22  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.97/2.22  thf(sk_B_type, type, sk_B: $i).
% 1.97/2.22  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.97/2.22  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.97/2.22  thf(sk_A_type, type, sk_A: $i).
% 1.97/2.22  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.97/2.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.97/2.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.97/2.22  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.97/2.22  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.97/2.22  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.97/2.22  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.97/2.22  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.97/2.22  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.97/2.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.97/2.22  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.97/2.22  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.97/2.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.97/2.22  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.97/2.22  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.97/2.22  thf(t76_tops_1, conjecture,
% 1.97/2.22    (![A:$i]:
% 1.97/2.22     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.97/2.22       ( ![B:$i]:
% 1.97/2.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.22           ( ( v3_pre_topc @ B @ A ) <=>
% 1.97/2.22             ( ( k2_tops_1 @ A @ B ) =
% 1.97/2.22               ( k7_subset_1 @
% 1.97/2.22                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 1.97/2.22  thf(zf_stmt_0, negated_conjecture,
% 1.97/2.22    (~( ![A:$i]:
% 1.97/2.22        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.97/2.22          ( ![B:$i]:
% 1.97/2.22            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.22              ( ( v3_pre_topc @ B @ A ) <=>
% 1.97/2.22                ( ( k2_tops_1 @ A @ B ) =
% 1.97/2.22                  ( k7_subset_1 @
% 1.97/2.22                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 1.97/2.22    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 1.97/2.22  thf('0', plain,
% 1.97/2.22      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.97/2.22        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf('1', plain,
% 1.97/2.22      (~
% 1.97/2.22       (((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.97/2.22       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.97/2.22      inference('split', [status(esa)], ['0'])).
% 1.97/2.22  thf('2', plain,
% 1.97/2.22      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf('3', plain,
% 1.97/2.22      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.97/2.22        | (v3_pre_topc @ sk_B @ sk_A))),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf('4', plain,
% 1.97/2.22      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.97/2.22      inference('split', [status(esa)], ['3'])).
% 1.97/2.22  thf('5', plain,
% 1.97/2.22      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf(t56_tops_1, axiom,
% 1.97/2.22    (![A:$i]:
% 1.97/2.22     ( ( l1_pre_topc @ A ) =>
% 1.97/2.22       ( ![B:$i]:
% 1.97/2.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.22           ( ![C:$i]:
% 1.97/2.22             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.22               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.97/2.22                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.97/2.22  thf('6', plain,
% 1.97/2.22      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.97/2.22         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 1.97/2.22          | ~ (v3_pre_topc @ X50 @ X51)
% 1.97/2.22          | ~ (r1_tarski @ X50 @ X52)
% 1.97/2.22          | (r1_tarski @ X50 @ (k1_tops_1 @ X51 @ X52))
% 1.97/2.22          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 1.97/2.22          | ~ (l1_pre_topc @ X51))),
% 1.97/2.22      inference('cnf', [status(esa)], [t56_tops_1])).
% 1.97/2.22  thf('7', plain,
% 1.97/2.22      (![X0 : $i]:
% 1.97/2.22         (~ (l1_pre_topc @ sk_A)
% 1.97/2.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.97/2.22          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.97/2.22          | ~ (r1_tarski @ sk_B @ X0)
% 1.97/2.22          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.97/2.22      inference('sup-', [status(thm)], ['5', '6'])).
% 1.97/2.22  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf('9', plain,
% 1.97/2.22      (![X0 : $i]:
% 1.97/2.22         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.97/2.22          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.97/2.22          | ~ (r1_tarski @ sk_B @ X0)
% 1.97/2.22          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.97/2.22      inference('demod', [status(thm)], ['7', '8'])).
% 1.97/2.22  thf('10', plain,
% 1.97/2.22      ((![X0 : $i]:
% 1.97/2.22          (~ (r1_tarski @ sk_B @ X0)
% 1.97/2.22           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.97/2.22           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.97/2.22         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.97/2.22      inference('sup-', [status(thm)], ['4', '9'])).
% 1.97/2.22  thf('11', plain,
% 1.97/2.22      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.97/2.22         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.97/2.22      inference('sup-', [status(thm)], ['2', '10'])).
% 1.97/2.22  thf(d10_xboole_0, axiom,
% 1.97/2.22    (![A:$i,B:$i]:
% 1.97/2.22     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.97/2.22  thf('12', plain,
% 1.97/2.22      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 1.97/2.22      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.97/2.22  thf('13', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.97/2.22      inference('simplify', [status(thm)], ['12'])).
% 1.97/2.22  thf('14', plain,
% 1.97/2.22      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.97/2.22         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.97/2.22      inference('demod', [status(thm)], ['11', '13'])).
% 1.97/2.22  thf('15', plain,
% 1.97/2.22      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf(t74_tops_1, axiom,
% 1.97/2.22    (![A:$i]:
% 1.97/2.22     ( ( l1_pre_topc @ A ) =>
% 1.97/2.22       ( ![B:$i]:
% 1.97/2.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.22           ( ( k1_tops_1 @ A @ B ) =
% 1.97/2.22             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.97/2.22  thf('16', plain,
% 1.97/2.22      (![X57 : $i, X58 : $i]:
% 1.97/2.22         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 1.97/2.22          | ((k1_tops_1 @ X58 @ X57)
% 1.97/2.22              = (k7_subset_1 @ (u1_struct_0 @ X58) @ X57 @ 
% 1.97/2.22                 (k2_tops_1 @ X58 @ X57)))
% 1.97/2.22          | ~ (l1_pre_topc @ X58))),
% 1.97/2.22      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.97/2.22  thf('17', plain,
% 1.97/2.22      ((~ (l1_pre_topc @ sk_A)
% 1.97/2.22        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.97/2.22            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.97/2.22               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.97/2.22      inference('sup-', [status(thm)], ['15', '16'])).
% 1.97/2.22  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf('19', plain,
% 1.97/2.22      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf(redefinition_k7_subset_1, axiom,
% 1.97/2.22    (![A:$i,B:$i,C:$i]:
% 1.97/2.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.97/2.22       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.97/2.22  thf('20', plain,
% 1.97/2.22      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.97/2.22         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 1.97/2.22          | ((k7_subset_1 @ X37 @ X36 @ X38) = (k4_xboole_0 @ X36 @ X38)))),
% 1.97/2.22      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.97/2.22  thf('21', plain,
% 1.97/2.22      (![X0 : $i]:
% 1.97/2.22         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.97/2.22           = (k4_xboole_0 @ sk_B @ X0))),
% 1.97/2.22      inference('sup-', [status(thm)], ['19', '20'])).
% 1.97/2.22  thf('22', plain,
% 1.97/2.22      (((k1_tops_1 @ sk_A @ sk_B)
% 1.97/2.22         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.97/2.22      inference('demod', [status(thm)], ['17', '18', '21'])).
% 1.97/2.22  thf(t36_xboole_1, axiom,
% 1.97/2.22    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.97/2.22  thf('23', plain,
% 1.97/2.22      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 1.97/2.22      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.97/2.22  thf('24', plain,
% 1.97/2.22      (![X1 : $i, X3 : $i]:
% 1.97/2.22         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.97/2.22      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.97/2.22  thf('25', plain,
% 1.97/2.22      (![X0 : $i, X1 : $i]:
% 1.97/2.22         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.97/2.22          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.97/2.22      inference('sup-', [status(thm)], ['23', '24'])).
% 1.97/2.22  thf('26', plain,
% 1.97/2.22      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.97/2.22        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.97/2.22      inference('sup-', [status(thm)], ['22', '25'])).
% 1.97/2.22  thf('27', plain,
% 1.97/2.22      (((k1_tops_1 @ sk_A @ sk_B)
% 1.97/2.22         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.97/2.22      inference('demod', [status(thm)], ['17', '18', '21'])).
% 1.97/2.22  thf('28', plain,
% 1.97/2.22      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.97/2.22        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 1.97/2.22      inference('demod', [status(thm)], ['26', '27'])).
% 1.97/2.22  thf('29', plain,
% 1.97/2.22      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 1.97/2.22         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.97/2.22      inference('sup-', [status(thm)], ['14', '28'])).
% 1.97/2.22  thf('30', plain,
% 1.97/2.22      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf(l78_tops_1, axiom,
% 1.97/2.22    (![A:$i]:
% 1.97/2.22     ( ( l1_pre_topc @ A ) =>
% 1.97/2.22       ( ![B:$i]:
% 1.97/2.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.22           ( ( k2_tops_1 @ A @ B ) =
% 1.97/2.22             ( k7_subset_1 @
% 1.97/2.22               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.97/2.22               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.97/2.22  thf('31', plain,
% 1.97/2.22      (![X48 : $i, X49 : $i]:
% 1.97/2.22         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 1.97/2.22          | ((k2_tops_1 @ X49 @ X48)
% 1.97/2.22              = (k7_subset_1 @ (u1_struct_0 @ X49) @ 
% 1.97/2.22                 (k2_pre_topc @ X49 @ X48) @ (k1_tops_1 @ X49 @ X48)))
% 1.97/2.22          | ~ (l1_pre_topc @ X49))),
% 1.97/2.22      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.97/2.22  thf('32', plain,
% 1.97/2.22      ((~ (l1_pre_topc @ sk_A)
% 1.97/2.22        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.97/2.22      inference('sup-', [status(thm)], ['30', '31'])).
% 1.97/2.22  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf('34', plain,
% 1.97/2.22      (((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.97/2.22            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.97/2.22      inference('demod', [status(thm)], ['32', '33'])).
% 1.97/2.22  thf('35', plain,
% 1.97/2.22      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.97/2.22         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.97/2.22      inference('sup+', [status(thm)], ['29', '34'])).
% 1.97/2.22  thf('36', plain,
% 1.97/2.22      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.97/2.22         <= (~
% 1.97/2.22             (((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.97/2.22      inference('split', [status(esa)], ['0'])).
% 1.97/2.22  thf('37', plain,
% 1.97/2.22      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.97/2.22         <= (~
% 1.97/2.22             (((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 1.97/2.22             ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.97/2.22      inference('sup-', [status(thm)], ['35', '36'])).
% 1.97/2.22  thf('38', plain,
% 1.97/2.22      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.97/2.22       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.97/2.22      inference('simplify', [status(thm)], ['37'])).
% 1.97/2.22  thf('39', plain,
% 1.97/2.22      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.97/2.22       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.97/2.22      inference('split', [status(esa)], ['3'])).
% 1.97/2.22  thf('40', plain,
% 1.97/2.22      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf(dt_k2_tops_1, axiom,
% 1.97/2.22    (![A:$i,B:$i]:
% 1.97/2.22     ( ( ( l1_pre_topc @ A ) & 
% 1.97/2.22         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.97/2.22       ( m1_subset_1 @
% 1.97/2.22         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.97/2.22  thf('41', plain,
% 1.97/2.22      (![X44 : $i, X45 : $i]:
% 1.97/2.22         (~ (l1_pre_topc @ X44)
% 1.97/2.22          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 1.97/2.22          | (m1_subset_1 @ (k2_tops_1 @ X44 @ X45) @ 
% 1.97/2.22             (k1_zfmisc_1 @ (u1_struct_0 @ X44))))),
% 1.97/2.22      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.97/2.22  thf('42', plain,
% 1.97/2.22      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.22         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.97/2.22        | ~ (l1_pre_topc @ sk_A))),
% 1.97/2.22      inference('sup-', [status(thm)], ['40', '41'])).
% 1.97/2.22  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf('44', plain,
% 1.97/2.22      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.22        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.22      inference('demod', [status(thm)], ['42', '43'])).
% 1.97/2.22  thf('45', plain,
% 1.97/2.22      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf(dt_k4_subset_1, axiom,
% 1.97/2.22    (![A:$i,B:$i,C:$i]:
% 1.97/2.22     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.97/2.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.97/2.22       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.97/2.22  thf('46', plain,
% 1.97/2.22      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.97/2.22         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 1.97/2.22          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 1.97/2.22          | (m1_subset_1 @ (k4_subset_1 @ X29 @ X28 @ X30) @ 
% 1.97/2.22             (k1_zfmisc_1 @ X29)))),
% 1.97/2.22      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 1.97/2.22  thf('47', plain,
% 1.97/2.22      (![X0 : $i]:
% 1.97/2.22         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.97/2.22           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.97/2.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.97/2.22      inference('sup-', [status(thm)], ['45', '46'])).
% 1.97/2.22  thf('48', plain,
% 1.97/2.22      ((m1_subset_1 @ 
% 1.97/2.22        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.97/2.22        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.22      inference('sup-', [status(thm)], ['44', '47'])).
% 1.97/2.22  thf('49', plain,
% 1.97/2.22      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf(t65_tops_1, axiom,
% 1.97/2.22    (![A:$i]:
% 1.97/2.22     ( ( l1_pre_topc @ A ) =>
% 1.97/2.22       ( ![B:$i]:
% 1.97/2.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.22           ( ( k2_pre_topc @ A @ B ) =
% 1.97/2.22             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.97/2.22  thf('50', plain,
% 1.97/2.22      (![X55 : $i, X56 : $i]:
% 1.97/2.22         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 1.97/2.22          | ((k2_pre_topc @ X56 @ X55)
% 1.97/2.22              = (k4_subset_1 @ (u1_struct_0 @ X56) @ X55 @ 
% 1.97/2.22                 (k2_tops_1 @ X56 @ X55)))
% 1.97/2.22          | ~ (l1_pre_topc @ X56))),
% 1.97/2.22      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.97/2.22  thf('51', plain,
% 1.97/2.22      ((~ (l1_pre_topc @ sk_A)
% 1.97/2.22        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.97/2.22            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.97/2.22               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.97/2.22      inference('sup-', [status(thm)], ['49', '50'])).
% 1.97/2.22  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf('53', plain,
% 1.97/2.22      (((k2_pre_topc @ sk_A @ sk_B)
% 1.97/2.22         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.97/2.22            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.97/2.22      inference('demod', [status(thm)], ['51', '52'])).
% 1.97/2.22  thf('54', plain,
% 1.97/2.22      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.97/2.22        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.22      inference('demod', [status(thm)], ['48', '53'])).
% 1.97/2.22  thf('55', plain,
% 1.97/2.22      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.97/2.22         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 1.97/2.22          | ((k7_subset_1 @ X37 @ X36 @ X38) = (k4_xboole_0 @ X36 @ X38)))),
% 1.97/2.22      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.97/2.22  thf('56', plain,
% 1.97/2.22      (![X0 : $i]:
% 1.97/2.22         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.97/2.22           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.97/2.22      inference('sup-', [status(thm)], ['54', '55'])).
% 1.97/2.22  thf('57', plain,
% 1.97/2.22      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.97/2.22         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.97/2.22      inference('split', [status(esa)], ['3'])).
% 1.97/2.22  thf('58', plain,
% 1.97/2.22      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.97/2.22         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.97/2.22      inference('sup+', [status(thm)], ['56', '57'])).
% 1.97/2.22  thf(idempotence_k3_xboole_0, axiom,
% 1.97/2.22    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.97/2.22  thf('59', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.97/2.22      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.97/2.22  thf(t12_setfam_1, axiom,
% 1.97/2.22    (![A:$i,B:$i]:
% 1.97/2.22     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.97/2.22  thf('60', plain,
% 1.97/2.22      (![X39 : $i, X40 : $i]:
% 1.97/2.22         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 1.97/2.22      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.97/2.22  thf('61', plain,
% 1.97/2.22      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.97/2.22      inference('demod', [status(thm)], ['59', '60'])).
% 1.97/2.22  thf(t100_xboole_1, axiom,
% 1.97/2.22    (![A:$i,B:$i]:
% 1.97/2.22     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.97/2.22  thf('62', plain,
% 1.97/2.22      (![X4 : $i, X5 : $i]:
% 1.97/2.22         ((k4_xboole_0 @ X4 @ X5)
% 1.97/2.22           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.97/2.22      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.97/2.22  thf('63', plain,
% 1.97/2.22      (![X39 : $i, X40 : $i]:
% 1.97/2.22         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 1.97/2.22      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.97/2.22  thf('64', plain,
% 1.97/2.22      (![X4 : $i, X5 : $i]:
% 1.97/2.22         ((k4_xboole_0 @ X4 @ X5)
% 1.97/2.22           = (k5_xboole_0 @ X4 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 1.97/2.22      inference('demod', [status(thm)], ['62', '63'])).
% 1.97/2.22  thf('65', plain,
% 1.97/2.22      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.97/2.22      inference('sup+', [status(thm)], ['61', '64'])).
% 1.97/2.22  thf(t49_xboole_1, axiom,
% 1.97/2.22    (![A:$i,B:$i,C:$i]:
% 1.97/2.22     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.97/2.22       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.97/2.22  thf('66', plain,
% 1.97/2.22      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.97/2.22         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 1.97/2.22           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 1.97/2.22      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.97/2.22  thf('67', plain,
% 1.97/2.22      (![X39 : $i, X40 : $i]:
% 1.97/2.22         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 1.97/2.22      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.97/2.22  thf('68', plain,
% 1.97/2.22      (![X39 : $i, X40 : $i]:
% 1.97/2.22         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 1.97/2.22      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.97/2.22  thf('69', plain,
% 1.97/2.22      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.97/2.22         ((k1_setfam_1 @ (k2_tarski @ X19 @ (k4_xboole_0 @ X20 @ X21)))
% 1.97/2.22           = (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X19 @ X20)) @ X21))),
% 1.97/2.22      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.97/2.22  thf('70', plain,
% 1.97/2.22      (![X4 : $i, X5 : $i]:
% 1.97/2.22         ((k4_xboole_0 @ X4 @ X5)
% 1.97/2.22           = (k5_xboole_0 @ X4 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 1.97/2.22      inference('demod', [status(thm)], ['62', '63'])).
% 1.97/2.22  thf('71', plain,
% 1.97/2.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.22         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 1.97/2.22           = (k5_xboole_0 @ X2 @ 
% 1.97/2.22              (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X1)) @ X0)))),
% 1.97/2.22      inference('sup+', [status(thm)], ['69', '70'])).
% 1.97/2.22  thf('72', plain,
% 1.97/2.22      (![X0 : $i, X1 : $i]:
% 1.97/2.22         ((k4_xboole_0 @ X1 @ 
% 1.97/2.22           (k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 1.97/2.22           = (k5_xboole_0 @ X1 @ 
% 1.97/2.22              (k5_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 1.97/2.22               (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 1.97/2.22      inference('sup+', [status(thm)], ['65', '71'])).
% 1.97/2.22  thf(commutativity_k2_tarski, axiom,
% 1.97/2.22    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.97/2.22  thf('73', plain,
% 1.97/2.22      (![X22 : $i, X23 : $i]:
% 1.97/2.22         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 1.97/2.22      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.97/2.22  thf(t47_xboole_1, axiom,
% 1.97/2.22    (![A:$i,B:$i]:
% 1.97/2.22     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.97/2.22  thf('74', plain,
% 1.97/2.22      (![X15 : $i, X16 : $i]:
% 1.97/2.22         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 1.97/2.22           = (k4_xboole_0 @ X15 @ X16))),
% 1.97/2.22      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.97/2.22  thf('75', plain,
% 1.97/2.22      (![X39 : $i, X40 : $i]:
% 1.97/2.22         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 1.97/2.22      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.97/2.22  thf('76', plain,
% 1.97/2.22      (![X15 : $i, X16 : $i]:
% 1.97/2.22         ((k4_xboole_0 @ X15 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16)))
% 1.97/2.22           = (k4_xboole_0 @ X15 @ X16))),
% 1.97/2.22      inference('demod', [status(thm)], ['74', '75'])).
% 1.97/2.22  thf('77', plain,
% 1.97/2.22      (![X0 : $i, X1 : $i]:
% 1.97/2.22         ((k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.97/2.22           = (k4_xboole_0 @ X0 @ X1))),
% 1.97/2.22      inference('sup+', [status(thm)], ['73', '76'])).
% 1.97/2.22  thf('78', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.97/2.22      inference('simplify', [status(thm)], ['12'])).
% 1.97/2.22  thf(t3_subset, axiom,
% 1.97/2.22    (![A:$i,B:$i]:
% 1.97/2.22     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.97/2.22  thf('79', plain,
% 1.97/2.22      (![X41 : $i, X43 : $i]:
% 1.97/2.22         ((m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X43)) | ~ (r1_tarski @ X41 @ X43))),
% 1.97/2.22      inference('cnf', [status(esa)], [t3_subset])).
% 1.97/2.22  thf('80', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.97/2.22      inference('sup-', [status(thm)], ['78', '79'])).
% 1.97/2.22  thf(d5_subset_1, axiom,
% 1.97/2.22    (![A:$i,B:$i]:
% 1.97/2.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.97/2.22       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.97/2.22  thf('81', plain,
% 1.97/2.22      (![X24 : $i, X25 : $i]:
% 1.97/2.22         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 1.97/2.22          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 1.97/2.22      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.97/2.22  thf('82', plain,
% 1.97/2.22      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.97/2.22      inference('sup-', [status(thm)], ['80', '81'])).
% 1.97/2.22  thf(t3_boole, axiom,
% 1.97/2.22    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.97/2.22  thf('83', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 1.97/2.22      inference('cnf', [status(esa)], [t3_boole])).
% 1.97/2.22  thf(t48_xboole_1, axiom,
% 1.97/2.22    (![A:$i,B:$i]:
% 1.97/2.22     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.97/2.22  thf('84', plain,
% 1.97/2.22      (![X17 : $i, X18 : $i]:
% 1.97/2.22         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.97/2.22           = (k3_xboole_0 @ X17 @ X18))),
% 1.97/2.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.97/2.22  thf('85', plain,
% 1.97/2.22      (![X39 : $i, X40 : $i]:
% 1.97/2.22         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 1.97/2.22      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.97/2.22  thf('86', plain,
% 1.97/2.22      (![X17 : $i, X18 : $i]:
% 1.97/2.22         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.97/2.22           = (k1_setfam_1 @ (k2_tarski @ X17 @ X18)))),
% 1.97/2.22      inference('demod', [status(thm)], ['84', '85'])).
% 1.97/2.22  thf('87', plain,
% 1.97/2.22      (![X0 : $i]:
% 1.97/2.22         ((k4_xboole_0 @ X0 @ X0)
% 1.97/2.22           = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 1.97/2.22      inference('sup+', [status(thm)], ['83', '86'])).
% 1.97/2.22  thf('88', plain,
% 1.97/2.22      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.97/2.22      inference('sup-', [status(thm)], ['80', '81'])).
% 1.97/2.22  thf(t2_boole, axiom,
% 1.97/2.22    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.97/2.22  thf('89', plain,
% 1.97/2.22      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.97/2.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.97/2.22  thf('90', plain,
% 1.97/2.22      (![X39 : $i, X40 : $i]:
% 1.97/2.22         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 1.97/2.22      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.97/2.22  thf('91', plain,
% 1.97/2.22      (![X8 : $i]:
% 1.97/2.22         ((k1_setfam_1 @ (k2_tarski @ X8 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.97/2.22      inference('demod', [status(thm)], ['89', '90'])).
% 1.97/2.22  thf('92', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.97/2.22      inference('demod', [status(thm)], ['87', '88', '91'])).
% 1.97/2.22  thf('93', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.97/2.22      inference('demod', [status(thm)], ['82', '92'])).
% 1.97/2.22  thf('94', plain,
% 1.97/2.22      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.97/2.22      inference('sup+', [status(thm)], ['61', '64'])).
% 1.97/2.22  thf('95', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.97/2.22      inference('sup+', [status(thm)], ['93', '94'])).
% 1.97/2.22  thf('96', plain,
% 1.97/2.22      (![X8 : $i]:
% 1.97/2.22         ((k1_setfam_1 @ (k2_tarski @ X8 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.97/2.22      inference('demod', [status(thm)], ['89', '90'])).
% 1.97/2.22  thf('97', plain,
% 1.97/2.22      (![X4 : $i, X5 : $i]:
% 1.97/2.22         ((k4_xboole_0 @ X4 @ X5)
% 1.97/2.22           = (k5_xboole_0 @ X4 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 1.97/2.22      inference('demod', [status(thm)], ['62', '63'])).
% 1.97/2.22  thf('98', plain,
% 1.97/2.22      (![X0 : $i]:
% 1.97/2.22         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.97/2.22      inference('sup+', [status(thm)], ['96', '97'])).
% 1.97/2.22  thf('99', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 1.97/2.22      inference('cnf', [status(esa)], [t3_boole])).
% 1.97/2.22  thf('100', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.97/2.22      inference('sup+', [status(thm)], ['98', '99'])).
% 1.97/2.22  thf('101', plain,
% 1.97/2.22      (![X0 : $i, X1 : $i]:
% 1.97/2.22         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (X1))),
% 1.97/2.22      inference('demod', [status(thm)], ['72', '77', '95', '100'])).
% 1.97/2.22  thf('102', plain,
% 1.97/2.22      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.97/2.22         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.97/2.22      inference('sup+', [status(thm)], ['58', '101'])).
% 1.97/2.22  thf('103', plain,
% 1.97/2.22      (((k1_tops_1 @ sk_A @ sk_B)
% 1.97/2.22         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.97/2.22      inference('demod', [status(thm)], ['17', '18', '21'])).
% 1.97/2.22  thf('104', plain,
% 1.97/2.22      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.97/2.22         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.97/2.22      inference('sup+', [status(thm)], ['102', '103'])).
% 1.97/2.22  thf('105', plain,
% 1.97/2.22      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf(fc9_tops_1, axiom,
% 1.97/2.22    (![A:$i,B:$i]:
% 1.97/2.22     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.97/2.22         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.97/2.22       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.97/2.22  thf('106', plain,
% 1.97/2.22      (![X46 : $i, X47 : $i]:
% 1.97/2.22         (~ (l1_pre_topc @ X46)
% 1.97/2.22          | ~ (v2_pre_topc @ X46)
% 1.97/2.22          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 1.97/2.22          | (v3_pre_topc @ (k1_tops_1 @ X46 @ X47) @ X46))),
% 1.97/2.22      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.97/2.22  thf('107', plain,
% 1.97/2.22      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.97/2.22        | ~ (v2_pre_topc @ sk_A)
% 1.97/2.22        | ~ (l1_pre_topc @ sk_A))),
% 1.97/2.22      inference('sup-', [status(thm)], ['105', '106'])).
% 1.97/2.22  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 1.97/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.22  thf('110', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.97/2.22      inference('demod', [status(thm)], ['107', '108', '109'])).
% 1.97/2.22  thf('111', plain,
% 1.97/2.22      (((v3_pre_topc @ sk_B @ sk_A))
% 1.97/2.22         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.97/2.22      inference('sup+', [status(thm)], ['104', '110'])).
% 1.97/2.22  thf('112', plain,
% 1.97/2.22      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.97/2.22      inference('split', [status(esa)], ['0'])).
% 1.97/2.22  thf('113', plain,
% 1.97/2.22      (~
% 1.97/2.22       (((k2_tops_1 @ sk_A @ sk_B)
% 1.97/2.22          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.22             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.97/2.22       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.97/2.22      inference('sup-', [status(thm)], ['111', '112'])).
% 1.97/2.22  thf('114', plain, ($false),
% 1.97/2.22      inference('sat_resolution*', [status(thm)], ['1', '38', '39', '113'])).
% 1.97/2.22  
% 1.97/2.22  % SZS output end Refutation
% 1.97/2.22  
% 2.06/2.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
