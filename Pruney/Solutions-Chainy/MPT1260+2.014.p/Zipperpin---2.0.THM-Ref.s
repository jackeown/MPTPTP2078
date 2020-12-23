%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9h4gEiMjQY

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:24 EST 2020

% Result     : Theorem 7.47s
% Output     : Refutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 286 expanded)
%              Number of leaves         :   41 ( 101 expanded)
%              Depth                    :   15
%              Number of atoms          : 1432 (3374 expanded)
%              Number of equality atoms :   93 ( 214 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( v3_pre_topc @ X52 @ X53 )
      | ~ ( r1_tarski @ X52 @ X54 )
      | ( r1_tarski @ X52 @ ( k1_tops_1 @ X53 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X53 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
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
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( ( k1_tops_1 @ X60 @ X59 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X60 ) @ X59 @ ( k2_tops_1 @ X60 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k4_xboole_0 @ X38 @ X40 ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X24 @ X25 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
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
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k2_tops_1 @ X51 @ X50 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X51 ) @ ( k2_pre_topc @ X51 @ X50 ) @ ( k1_tops_1 @ X51 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
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
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X34 @ X33 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) ) ) ),
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
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( ( k2_pre_topc @ X58 @ X57 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X58 ) @ X57 @ ( k2_tops_1 @ X58 @ X57 ) ) )
      | ~ ( l1_pre_topc @ X58 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k4_xboole_0 @ X38 @ X40 ) ) ) ),
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

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('62',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X18 @ X20 ) @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('63',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('64',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('65',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('66',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X18 @ X20 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k5_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('69',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('71',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('72',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('73',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('74',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('75',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('76',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('81',plain,(
    ! [X23: $i] :
      ( ( k3_xboole_0 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('82',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('83',plain,(
    ! [X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('87',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('88',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('90',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','90'])).

thf('92',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['70','94'])).

thf('96',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('99',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['97','102'])).

thf('104',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['58','103'])).

thf('105',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('106',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('108',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X48 @ X49 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('109',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['106','112'])).

thf('114',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('115',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','38','39','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9h4gEiMjQY
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 7.47/7.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.47/7.69  % Solved by: fo/fo7.sh
% 7.47/7.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.47/7.69  % done 6141 iterations in 7.232s
% 7.47/7.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.47/7.69  % SZS output start Refutation
% 7.47/7.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.47/7.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.47/7.69  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 7.47/7.69  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 7.47/7.69  thf(sk_B_type, type, sk_B: $i).
% 7.47/7.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.47/7.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.47/7.69  thf(sk_A_type, type, sk_A: $i).
% 7.47/7.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.47/7.69  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 7.47/7.69  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 7.47/7.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.47/7.69  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 7.47/7.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 7.47/7.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 7.47/7.69  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 7.47/7.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.47/7.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.47/7.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.47/7.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.47/7.69  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 7.47/7.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 7.47/7.69  thf(t76_tops_1, conjecture,
% 7.47/7.69    (![A:$i]:
% 7.47/7.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.47/7.69       ( ![B:$i]:
% 7.47/7.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.47/7.69           ( ( v3_pre_topc @ B @ A ) <=>
% 7.47/7.69             ( ( k2_tops_1 @ A @ B ) =
% 7.47/7.69               ( k7_subset_1 @
% 7.47/7.69                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 7.47/7.69  thf(zf_stmt_0, negated_conjecture,
% 7.47/7.69    (~( ![A:$i]:
% 7.47/7.69        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.47/7.69          ( ![B:$i]:
% 7.47/7.69            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.47/7.69              ( ( v3_pre_topc @ B @ A ) <=>
% 7.47/7.69                ( ( k2_tops_1 @ A @ B ) =
% 7.47/7.69                  ( k7_subset_1 @
% 7.47/7.69                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 7.47/7.69    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 7.47/7.69  thf('0', plain,
% 7.47/7.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 7.47/7.69        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf('1', plain,
% 7.47/7.69      (~
% 7.47/7.69       (((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 7.47/7.69       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 7.47/7.69      inference('split', [status(esa)], ['0'])).
% 7.47/7.69  thf('2', plain,
% 7.47/7.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf('3', plain,
% 7.47/7.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 7.47/7.69        | (v3_pre_topc @ sk_B @ sk_A))),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf('4', plain,
% 7.47/7.69      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 7.47/7.69      inference('split', [status(esa)], ['3'])).
% 7.47/7.69  thf('5', plain,
% 7.47/7.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf(t56_tops_1, axiom,
% 7.47/7.69    (![A:$i]:
% 7.47/7.69     ( ( l1_pre_topc @ A ) =>
% 7.47/7.69       ( ![B:$i]:
% 7.47/7.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.47/7.69           ( ![C:$i]:
% 7.47/7.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.47/7.69               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 7.47/7.69                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 7.47/7.69  thf('6', plain,
% 7.47/7.69      (![X52 : $i, X53 : $i, X54 : $i]:
% 7.47/7.69         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 7.47/7.69          | ~ (v3_pre_topc @ X52 @ X53)
% 7.47/7.69          | ~ (r1_tarski @ X52 @ X54)
% 7.47/7.69          | (r1_tarski @ X52 @ (k1_tops_1 @ X53 @ X54))
% 7.47/7.69          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 7.47/7.69          | ~ (l1_pre_topc @ X53))),
% 7.47/7.69      inference('cnf', [status(esa)], [t56_tops_1])).
% 7.47/7.69  thf('7', plain,
% 7.47/7.69      (![X0 : $i]:
% 7.47/7.69         (~ (l1_pre_topc @ sk_A)
% 7.47/7.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.47/7.69          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 7.47/7.69          | ~ (r1_tarski @ sk_B @ X0)
% 7.47/7.69          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 7.47/7.69      inference('sup-', [status(thm)], ['5', '6'])).
% 7.47/7.69  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf('9', plain,
% 7.47/7.69      (![X0 : $i]:
% 7.47/7.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.47/7.69          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 7.47/7.69          | ~ (r1_tarski @ sk_B @ X0)
% 7.47/7.69          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 7.47/7.69      inference('demod', [status(thm)], ['7', '8'])).
% 7.47/7.69  thf('10', plain,
% 7.47/7.69      ((![X0 : $i]:
% 7.47/7.69          (~ (r1_tarski @ sk_B @ X0)
% 7.47/7.69           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 7.47/7.69           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 7.47/7.69         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 7.47/7.69      inference('sup-', [status(thm)], ['4', '9'])).
% 7.47/7.69  thf('11', plain,
% 7.47/7.69      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 7.47/7.69         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 7.47/7.69      inference('sup-', [status(thm)], ['2', '10'])).
% 7.47/7.69  thf(d10_xboole_0, axiom,
% 7.47/7.69    (![A:$i,B:$i]:
% 7.47/7.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.47/7.69  thf('12', plain,
% 7.47/7.69      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 7.47/7.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.47/7.69  thf('13', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 7.47/7.69      inference('simplify', [status(thm)], ['12'])).
% 7.47/7.69  thf('14', plain,
% 7.47/7.69      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.47/7.69         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 7.47/7.69      inference('demod', [status(thm)], ['11', '13'])).
% 7.47/7.69  thf('15', plain,
% 7.47/7.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf(t74_tops_1, axiom,
% 7.47/7.69    (![A:$i]:
% 7.47/7.69     ( ( l1_pre_topc @ A ) =>
% 7.47/7.69       ( ![B:$i]:
% 7.47/7.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.47/7.69           ( ( k1_tops_1 @ A @ B ) =
% 7.47/7.69             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 7.47/7.69  thf('16', plain,
% 7.47/7.69      (![X59 : $i, X60 : $i]:
% 7.47/7.69         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 7.47/7.69          | ((k1_tops_1 @ X60 @ X59)
% 7.47/7.69              = (k7_subset_1 @ (u1_struct_0 @ X60) @ X59 @ 
% 7.47/7.69                 (k2_tops_1 @ X60 @ X59)))
% 7.47/7.69          | ~ (l1_pre_topc @ X60))),
% 7.47/7.69      inference('cnf', [status(esa)], [t74_tops_1])).
% 7.47/7.69  thf('17', plain,
% 7.47/7.69      ((~ (l1_pre_topc @ sk_A)
% 7.47/7.69        | ((k1_tops_1 @ sk_A @ sk_B)
% 7.47/7.69            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 7.47/7.69               (k2_tops_1 @ sk_A @ sk_B))))),
% 7.47/7.69      inference('sup-', [status(thm)], ['15', '16'])).
% 7.47/7.69  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf('19', plain,
% 7.47/7.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf(redefinition_k7_subset_1, axiom,
% 7.47/7.69    (![A:$i,B:$i,C:$i]:
% 7.47/7.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.47/7.69       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 7.47/7.69  thf('20', plain,
% 7.47/7.69      (![X38 : $i, X39 : $i, X40 : $i]:
% 7.47/7.69         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 7.47/7.69          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k4_xboole_0 @ X38 @ X40)))),
% 7.47/7.69      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 7.47/7.69  thf('21', plain,
% 7.47/7.69      (![X0 : $i]:
% 7.47/7.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 7.47/7.69           = (k4_xboole_0 @ sk_B @ X0))),
% 7.47/7.69      inference('sup-', [status(thm)], ['19', '20'])).
% 7.47/7.69  thf('22', plain,
% 7.47/7.69      (((k1_tops_1 @ sk_A @ sk_B)
% 7.47/7.69         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.47/7.69      inference('demod', [status(thm)], ['17', '18', '21'])).
% 7.47/7.69  thf(t36_xboole_1, axiom,
% 7.47/7.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 7.47/7.69  thf('23', plain,
% 7.47/7.69      (![X24 : $i, X25 : $i]: (r1_tarski @ (k4_xboole_0 @ X24 @ X25) @ X24)),
% 7.47/7.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 7.47/7.69  thf('24', plain,
% 7.47/7.69      (![X13 : $i, X15 : $i]:
% 7.47/7.69         (((X13) = (X15))
% 7.47/7.69          | ~ (r1_tarski @ X15 @ X13)
% 7.47/7.69          | ~ (r1_tarski @ X13 @ X15))),
% 7.47/7.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.47/7.69  thf('25', plain,
% 7.47/7.69      (![X0 : $i, X1 : $i]:
% 7.47/7.69         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 7.47/7.69          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 7.47/7.69      inference('sup-', [status(thm)], ['23', '24'])).
% 7.47/7.69  thf('26', plain,
% 7.47/7.69      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 7.47/7.69        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 7.47/7.69      inference('sup-', [status(thm)], ['22', '25'])).
% 7.47/7.69  thf('27', plain,
% 7.47/7.69      (((k1_tops_1 @ sk_A @ sk_B)
% 7.47/7.69         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.47/7.69      inference('demod', [status(thm)], ['17', '18', '21'])).
% 7.47/7.69  thf('28', plain,
% 7.47/7.69      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 7.47/7.69        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 7.47/7.69      inference('demod', [status(thm)], ['26', '27'])).
% 7.47/7.69  thf('29', plain,
% 7.47/7.69      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 7.47/7.69         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 7.47/7.69      inference('sup-', [status(thm)], ['14', '28'])).
% 7.47/7.69  thf('30', plain,
% 7.47/7.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf(l78_tops_1, axiom,
% 7.47/7.69    (![A:$i]:
% 7.47/7.69     ( ( l1_pre_topc @ A ) =>
% 7.47/7.69       ( ![B:$i]:
% 7.47/7.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.47/7.69           ( ( k2_tops_1 @ A @ B ) =
% 7.47/7.69             ( k7_subset_1 @
% 7.47/7.69               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 7.47/7.69               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 7.47/7.69  thf('31', plain,
% 7.47/7.69      (![X50 : $i, X51 : $i]:
% 7.47/7.69         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 7.47/7.69          | ((k2_tops_1 @ X51 @ X50)
% 7.47/7.69              = (k7_subset_1 @ (u1_struct_0 @ X51) @ 
% 7.47/7.69                 (k2_pre_topc @ X51 @ X50) @ (k1_tops_1 @ X51 @ X50)))
% 7.47/7.69          | ~ (l1_pre_topc @ X51))),
% 7.47/7.69      inference('cnf', [status(esa)], [l78_tops_1])).
% 7.47/7.69  thf('32', plain,
% 7.47/7.69      ((~ (l1_pre_topc @ sk_A)
% 7.47/7.69        | ((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 7.47/7.69      inference('sup-', [status(thm)], ['30', '31'])).
% 7.47/7.69  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf('34', plain,
% 7.47/7.69      (((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.47/7.69            (k1_tops_1 @ sk_A @ sk_B)))),
% 7.47/7.69      inference('demod', [status(thm)], ['32', '33'])).
% 7.47/7.69  thf('35', plain,
% 7.47/7.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 7.47/7.69         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 7.47/7.69      inference('sup+', [status(thm)], ['29', '34'])).
% 7.47/7.69  thf('36', plain,
% 7.47/7.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 7.47/7.69         <= (~
% 7.47/7.69             (((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 7.47/7.69      inference('split', [status(esa)], ['0'])).
% 7.47/7.69  thf('37', plain,
% 7.47/7.69      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 7.47/7.69         <= (~
% 7.47/7.69             (((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 7.47/7.69             ((v3_pre_topc @ sk_B @ sk_A)))),
% 7.47/7.69      inference('sup-', [status(thm)], ['35', '36'])).
% 7.47/7.69  thf('38', plain,
% 7.47/7.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 7.47/7.69       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 7.47/7.69      inference('simplify', [status(thm)], ['37'])).
% 7.47/7.69  thf('39', plain,
% 7.47/7.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 7.47/7.69       ((v3_pre_topc @ sk_B @ sk_A))),
% 7.47/7.69      inference('split', [status(esa)], ['3'])).
% 7.47/7.69  thf('40', plain,
% 7.47/7.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf(dt_k2_tops_1, axiom,
% 7.47/7.69    (![A:$i,B:$i]:
% 7.47/7.69     ( ( ( l1_pre_topc @ A ) & 
% 7.47/7.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.47/7.69       ( m1_subset_1 @
% 7.47/7.69         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.47/7.69  thf('41', plain,
% 7.47/7.69      (![X46 : $i, X47 : $i]:
% 7.47/7.69         (~ (l1_pre_topc @ X46)
% 7.47/7.69          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 7.47/7.69          | (m1_subset_1 @ (k2_tops_1 @ X46 @ X47) @ 
% 7.47/7.69             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 7.47/7.69      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 7.47/7.69  thf('42', plain,
% 7.47/7.69      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.47/7.69         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.47/7.69        | ~ (l1_pre_topc @ sk_A))),
% 7.47/7.69      inference('sup-', [status(thm)], ['40', '41'])).
% 7.47/7.69  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf('44', plain,
% 7.47/7.69      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 7.47/7.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.47/7.69      inference('demod', [status(thm)], ['42', '43'])).
% 7.47/7.69  thf('45', plain,
% 7.47/7.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf(dt_k4_subset_1, axiom,
% 7.47/7.69    (![A:$i,B:$i,C:$i]:
% 7.47/7.69     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 7.47/7.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 7.47/7.69       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 7.47/7.69  thf('46', plain,
% 7.47/7.69      (![X33 : $i, X34 : $i, X35 : $i]:
% 7.47/7.69         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 7.47/7.69          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34))
% 7.47/7.69          | (m1_subset_1 @ (k4_subset_1 @ X34 @ X33 @ X35) @ 
% 7.47/7.69             (k1_zfmisc_1 @ X34)))),
% 7.47/7.69      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 7.47/7.69  thf('47', plain,
% 7.47/7.69      (![X0 : $i]:
% 7.47/7.69         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 7.47/7.69           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.47/7.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.47/7.69      inference('sup-', [status(thm)], ['45', '46'])).
% 7.47/7.69  thf('48', plain,
% 7.47/7.69      ((m1_subset_1 @ 
% 7.47/7.69        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 7.47/7.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.47/7.69      inference('sup-', [status(thm)], ['44', '47'])).
% 7.47/7.69  thf('49', plain,
% 7.47/7.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf(t65_tops_1, axiom,
% 7.47/7.69    (![A:$i]:
% 7.47/7.69     ( ( l1_pre_topc @ A ) =>
% 7.47/7.69       ( ![B:$i]:
% 7.47/7.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.47/7.69           ( ( k2_pre_topc @ A @ B ) =
% 7.47/7.69             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 7.47/7.69  thf('50', plain,
% 7.47/7.69      (![X57 : $i, X58 : $i]:
% 7.47/7.69         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 7.47/7.69          | ((k2_pre_topc @ X58 @ X57)
% 7.47/7.69              = (k4_subset_1 @ (u1_struct_0 @ X58) @ X57 @ 
% 7.47/7.69                 (k2_tops_1 @ X58 @ X57)))
% 7.47/7.69          | ~ (l1_pre_topc @ X58))),
% 7.47/7.69      inference('cnf', [status(esa)], [t65_tops_1])).
% 7.47/7.69  thf('51', plain,
% 7.47/7.69      ((~ (l1_pre_topc @ sk_A)
% 7.47/7.69        | ((k2_pre_topc @ sk_A @ sk_B)
% 7.47/7.69            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 7.47/7.69               (k2_tops_1 @ sk_A @ sk_B))))),
% 7.47/7.69      inference('sup-', [status(thm)], ['49', '50'])).
% 7.47/7.69  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf('53', plain,
% 7.47/7.69      (((k2_pre_topc @ sk_A @ sk_B)
% 7.47/7.69         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 7.47/7.69            (k2_tops_1 @ sk_A @ sk_B)))),
% 7.47/7.69      inference('demod', [status(thm)], ['51', '52'])).
% 7.47/7.69  thf('54', plain,
% 7.47/7.69      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.47/7.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.47/7.69      inference('demod', [status(thm)], ['48', '53'])).
% 7.47/7.69  thf('55', plain,
% 7.47/7.69      (![X38 : $i, X39 : $i, X40 : $i]:
% 7.47/7.69         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 7.47/7.69          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k4_xboole_0 @ X38 @ X40)))),
% 7.47/7.69      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 7.47/7.69  thf('56', plain,
% 7.47/7.69      (![X0 : $i]:
% 7.47/7.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.47/7.69           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 7.47/7.69      inference('sup-', [status(thm)], ['54', '55'])).
% 7.47/7.69  thf('57', plain,
% 7.47/7.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 7.47/7.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 7.47/7.69      inference('split', [status(esa)], ['3'])).
% 7.47/7.69  thf('58', plain,
% 7.47/7.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 7.47/7.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 7.47/7.69      inference('sup+', [status(thm)], ['56', '57'])).
% 7.47/7.69  thf(t100_xboole_1, axiom,
% 7.47/7.69    (![A:$i,B:$i]:
% 7.47/7.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 7.47/7.69  thf('59', plain,
% 7.47/7.69      (![X16 : $i, X17 : $i]:
% 7.47/7.69         ((k4_xboole_0 @ X16 @ X17)
% 7.47/7.69           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 7.47/7.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 7.47/7.69  thf(t12_setfam_1, axiom,
% 7.47/7.69    (![A:$i,B:$i]:
% 7.47/7.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 7.47/7.69  thf('60', plain,
% 7.47/7.69      (![X41 : $i, X42 : $i]:
% 7.47/7.69         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 7.47/7.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.47/7.69  thf('61', plain,
% 7.47/7.69      (![X16 : $i, X17 : $i]:
% 7.47/7.69         ((k4_xboole_0 @ X16 @ X17)
% 7.47/7.69           = (k5_xboole_0 @ X16 @ (k1_setfam_1 @ (k2_tarski @ X16 @ X17))))),
% 7.47/7.69      inference('demod', [status(thm)], ['59', '60'])).
% 7.47/7.69  thf(t112_xboole_1, axiom,
% 7.47/7.69    (![A:$i,B:$i,C:$i]:
% 7.47/7.69     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 7.47/7.69       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 7.47/7.69  thf('62', plain,
% 7.47/7.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.47/7.69         ((k5_xboole_0 @ (k3_xboole_0 @ X18 @ X20) @ (k3_xboole_0 @ X19 @ X20))
% 7.47/7.69           = (k3_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20))),
% 7.47/7.69      inference('cnf', [status(esa)], [t112_xboole_1])).
% 7.47/7.69  thf('63', plain,
% 7.47/7.69      (![X41 : $i, X42 : $i]:
% 7.47/7.69         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 7.47/7.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.47/7.69  thf('64', plain,
% 7.47/7.69      (![X41 : $i, X42 : $i]:
% 7.47/7.69         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 7.47/7.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.47/7.69  thf('65', plain,
% 7.47/7.69      (![X41 : $i, X42 : $i]:
% 7.47/7.69         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 7.47/7.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.47/7.69  thf('66', plain,
% 7.47/7.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.47/7.69         ((k5_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X18 @ X20)) @ 
% 7.47/7.69           (k1_setfam_1 @ (k2_tarski @ X19 @ X20)))
% 7.47/7.69           = (k1_setfam_1 @ (k2_tarski @ (k5_xboole_0 @ X18 @ X19) @ X20)))),
% 7.47/7.69      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 7.47/7.69  thf('67', plain,
% 7.47/7.69      (![X0 : $i, X1 : $i]:
% 7.47/7.69         ((k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)
% 7.47/7.69           = (k1_setfam_1 @ 
% 7.47/7.69              (k2_tarski @ 
% 7.47/7.69               (k5_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ X0)))),
% 7.47/7.69      inference('sup+', [status(thm)], ['61', '66'])).
% 7.47/7.69  thf('68', plain,
% 7.47/7.69      (![X16 : $i, X17 : $i]:
% 7.47/7.69         ((k4_xboole_0 @ X16 @ X17)
% 7.47/7.69           = (k5_xboole_0 @ X16 @ (k1_setfam_1 @ (k2_tarski @ X16 @ X17))))),
% 7.47/7.69      inference('demod', [status(thm)], ['59', '60'])).
% 7.47/7.69  thf(commutativity_k2_tarski, axiom,
% 7.47/7.69    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 7.47/7.69  thf('69', plain,
% 7.47/7.69      (![X27 : $i, X28 : $i]:
% 7.47/7.69         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 7.47/7.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 7.47/7.69  thf('70', plain,
% 7.47/7.69      (![X0 : $i, X1 : $i]:
% 7.47/7.69         ((k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)
% 7.47/7.69           = (k1_setfam_1 @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 7.47/7.69      inference('demod', [status(thm)], ['67', '68', '69'])).
% 7.47/7.69  thf(d4_xboole_0, axiom,
% 7.47/7.69    (![A:$i,B:$i,C:$i]:
% 7.47/7.69     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 7.47/7.69       ( ![D:$i]:
% 7.47/7.69         ( ( r2_hidden @ D @ C ) <=>
% 7.47/7.69           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 7.47/7.69  thf('71', plain,
% 7.47/7.69      (![X1 : $i, X2 : $i, X5 : $i]:
% 7.47/7.69         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 7.47/7.69          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 7.47/7.69          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 7.47/7.69      inference('cnf', [status(esa)], [d4_xboole_0])).
% 7.47/7.69  thf('72', plain,
% 7.47/7.69      (![X41 : $i, X42 : $i]:
% 7.47/7.69         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 7.47/7.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.47/7.69  thf('73', plain,
% 7.47/7.69      (![X1 : $i, X2 : $i, X5 : $i]:
% 7.47/7.69         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 7.47/7.69          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 7.47/7.69          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 7.47/7.69      inference('demod', [status(thm)], ['71', '72'])).
% 7.47/7.69  thf(t3_boole, axiom,
% 7.47/7.69    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 7.47/7.69  thf('74', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 7.47/7.69      inference('cnf', [status(esa)], [t3_boole])).
% 7.47/7.69  thf(d5_xboole_0, axiom,
% 7.47/7.69    (![A:$i,B:$i,C:$i]:
% 7.47/7.69     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 7.47/7.69       ( ![D:$i]:
% 7.47/7.69         ( ( r2_hidden @ D @ C ) <=>
% 7.47/7.69           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 7.47/7.69  thf('75', plain,
% 7.47/7.69      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 7.47/7.69         (~ (r2_hidden @ X10 @ X9)
% 7.47/7.69          | ~ (r2_hidden @ X10 @ X8)
% 7.47/7.69          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 7.47/7.69      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.47/7.69  thf('76', plain,
% 7.47/7.69      (![X7 : $i, X8 : $i, X10 : $i]:
% 7.47/7.69         (~ (r2_hidden @ X10 @ X8)
% 7.47/7.69          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 7.47/7.69      inference('simplify', [status(thm)], ['75'])).
% 7.47/7.69  thf('77', plain,
% 7.47/7.69      (![X0 : $i, X1 : $i]:
% 7.47/7.69         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 7.47/7.69      inference('sup-', [status(thm)], ['74', '76'])).
% 7.47/7.69  thf('78', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 7.47/7.69      inference('condensation', [status(thm)], ['77'])).
% 7.47/7.69  thf('79', plain,
% 7.47/7.69      (![X0 : $i, X1 : $i]:
% 7.47/7.69         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 7.47/7.69          | ((X1) = (k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0))))),
% 7.47/7.69      inference('sup-', [status(thm)], ['73', '78'])).
% 7.47/7.69  thf('80', plain,
% 7.47/7.69      (![X27 : $i, X28 : $i]:
% 7.47/7.69         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 7.47/7.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 7.47/7.69  thf(t2_boole, axiom,
% 7.47/7.69    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 7.47/7.69  thf('81', plain,
% 7.47/7.69      (![X23 : $i]: ((k3_xboole_0 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 7.47/7.69      inference('cnf', [status(esa)], [t2_boole])).
% 7.47/7.69  thf('82', plain,
% 7.47/7.69      (![X41 : $i, X42 : $i]:
% 7.47/7.69         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 7.47/7.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.47/7.69  thf('83', plain,
% 7.47/7.69      (![X23 : $i]:
% 7.47/7.69         ((k1_setfam_1 @ (k2_tarski @ X23 @ k1_xboole_0)) = (k1_xboole_0))),
% 7.47/7.69      inference('demod', [status(thm)], ['81', '82'])).
% 7.47/7.69  thf('84', plain,
% 7.47/7.69      (![X0 : $i]:
% 7.47/7.69         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 7.47/7.69      inference('sup+', [status(thm)], ['80', '83'])).
% 7.47/7.69  thf('85', plain,
% 7.47/7.69      (![X0 : $i, X1 : $i]:
% 7.47/7.69         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 7.47/7.69          | ((X1) = (k1_xboole_0)))),
% 7.47/7.69      inference('demod', [status(thm)], ['79', '84'])).
% 7.47/7.69  thf('86', plain,
% 7.47/7.69      (![X0 : $i, X1 : $i]:
% 7.47/7.69         ((k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)
% 7.47/7.69           = (k1_setfam_1 @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 7.47/7.69      inference('demod', [status(thm)], ['67', '68', '69'])).
% 7.47/7.69  thf('87', plain,
% 7.47/7.69      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 7.47/7.69         (~ (r2_hidden @ X4 @ X3)
% 7.47/7.69          | (r2_hidden @ X4 @ X1)
% 7.47/7.69          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 7.47/7.69      inference('cnf', [status(esa)], [d4_xboole_0])).
% 7.47/7.69  thf('88', plain,
% 7.47/7.69      (![X1 : $i, X2 : $i, X4 : $i]:
% 7.47/7.69         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 7.47/7.69      inference('simplify', [status(thm)], ['87'])).
% 7.47/7.69  thf('89', plain,
% 7.47/7.69      (![X41 : $i, X42 : $i]:
% 7.47/7.69         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 7.47/7.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.47/7.69  thf('90', plain,
% 7.47/7.69      (![X1 : $i, X2 : $i, X4 : $i]:
% 7.47/7.69         ((r2_hidden @ X4 @ X1)
% 7.47/7.69          | ~ (r2_hidden @ X4 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))))),
% 7.47/7.69      inference('demod', [status(thm)], ['88', '89'])).
% 7.47/7.69  thf('91', plain,
% 7.47/7.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.47/7.69         (~ (r2_hidden @ X2 @ 
% 7.47/7.69             (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0))
% 7.47/7.69          | (r2_hidden @ X2 @ X0))),
% 7.47/7.69      inference('sup-', [status(thm)], ['86', '90'])).
% 7.47/7.69  thf('92', plain,
% 7.47/7.69      (![X7 : $i, X8 : $i, X10 : $i]:
% 7.47/7.69         (~ (r2_hidden @ X10 @ X8)
% 7.47/7.69          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 7.47/7.69      inference('simplify', [status(thm)], ['75'])).
% 7.47/7.69  thf('93', plain,
% 7.47/7.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.47/7.69         ~ (r2_hidden @ X2 @ 
% 7.47/7.69            (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0))),
% 7.47/7.69      inference('clc', [status(thm)], ['91', '92'])).
% 7.47/7.69  thf('94', plain,
% 7.47/7.69      (![X0 : $i, X1 : $i]:
% 7.47/7.69         ((k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)
% 7.47/7.69           = (k1_xboole_0))),
% 7.47/7.69      inference('sup-', [status(thm)], ['85', '93'])).
% 7.47/7.69  thf('95', plain,
% 7.47/7.69      (![X0 : $i, X1 : $i]:
% 7.47/7.69         ((k1_xboole_0)
% 7.47/7.69           = (k1_setfam_1 @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 7.47/7.69      inference('demod', [status(thm)], ['70', '94'])).
% 7.47/7.69  thf('96', plain,
% 7.47/7.69      (![X16 : $i, X17 : $i]:
% 7.47/7.69         ((k4_xboole_0 @ X16 @ X17)
% 7.47/7.69           = (k5_xboole_0 @ X16 @ (k1_setfam_1 @ (k2_tarski @ X16 @ X17))))),
% 7.47/7.69      inference('demod', [status(thm)], ['59', '60'])).
% 7.47/7.69  thf('97', plain,
% 7.47/7.69      (![X0 : $i, X1 : $i]:
% 7.47/7.69         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 7.47/7.69           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 7.47/7.69      inference('sup+', [status(thm)], ['95', '96'])).
% 7.47/7.69  thf('98', plain,
% 7.47/7.69      (![X23 : $i]:
% 7.47/7.69         ((k1_setfam_1 @ (k2_tarski @ X23 @ k1_xboole_0)) = (k1_xboole_0))),
% 7.47/7.69      inference('demod', [status(thm)], ['81', '82'])).
% 7.47/7.69  thf('99', plain,
% 7.47/7.69      (![X16 : $i, X17 : $i]:
% 7.47/7.69         ((k4_xboole_0 @ X16 @ X17)
% 7.47/7.69           = (k5_xboole_0 @ X16 @ (k1_setfam_1 @ (k2_tarski @ X16 @ X17))))),
% 7.47/7.69      inference('demod', [status(thm)], ['59', '60'])).
% 7.47/7.69  thf('100', plain,
% 7.47/7.69      (![X0 : $i]:
% 7.47/7.69         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 7.47/7.69      inference('sup+', [status(thm)], ['98', '99'])).
% 7.47/7.69  thf('101', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 7.47/7.69      inference('cnf', [status(esa)], [t3_boole])).
% 7.47/7.69  thf('102', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 7.47/7.69      inference('sup+', [status(thm)], ['100', '101'])).
% 7.47/7.69  thf('103', plain,
% 7.47/7.69      (![X0 : $i, X1 : $i]:
% 7.47/7.69         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 7.47/7.69      inference('demod', [status(thm)], ['97', '102'])).
% 7.47/7.69  thf('104', plain,
% 7.47/7.69      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 7.47/7.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 7.47/7.69      inference('sup+', [status(thm)], ['58', '103'])).
% 7.47/7.69  thf('105', plain,
% 7.47/7.69      (((k1_tops_1 @ sk_A @ sk_B)
% 7.47/7.69         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 7.47/7.69      inference('demod', [status(thm)], ['17', '18', '21'])).
% 7.47/7.69  thf('106', plain,
% 7.47/7.69      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 7.47/7.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 7.47/7.69      inference('sup+', [status(thm)], ['104', '105'])).
% 7.47/7.69  thf('107', plain,
% 7.47/7.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf(fc9_tops_1, axiom,
% 7.47/7.69    (![A:$i,B:$i]:
% 7.47/7.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 7.47/7.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.47/7.69       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 7.47/7.69  thf('108', plain,
% 7.47/7.69      (![X48 : $i, X49 : $i]:
% 7.47/7.69         (~ (l1_pre_topc @ X48)
% 7.47/7.69          | ~ (v2_pre_topc @ X48)
% 7.47/7.69          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 7.47/7.69          | (v3_pre_topc @ (k1_tops_1 @ X48 @ X49) @ X48))),
% 7.47/7.69      inference('cnf', [status(esa)], [fc9_tops_1])).
% 7.47/7.69  thf('109', plain,
% 7.47/7.69      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 7.47/7.69        | ~ (v2_pre_topc @ sk_A)
% 7.47/7.69        | ~ (l1_pre_topc @ sk_A))),
% 7.47/7.69      inference('sup-', [status(thm)], ['107', '108'])).
% 7.47/7.69  thf('110', plain, ((v2_pre_topc @ sk_A)),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 7.47/7.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.47/7.69  thf('112', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 7.47/7.69      inference('demod', [status(thm)], ['109', '110', '111'])).
% 7.47/7.69  thf('113', plain,
% 7.47/7.69      (((v3_pre_topc @ sk_B @ sk_A))
% 7.47/7.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 7.47/7.69      inference('sup+', [status(thm)], ['106', '112'])).
% 7.47/7.69  thf('114', plain,
% 7.47/7.69      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 7.47/7.69      inference('split', [status(esa)], ['0'])).
% 7.47/7.69  thf('115', plain,
% 7.47/7.69      (~
% 7.47/7.69       (((k2_tops_1 @ sk_A @ sk_B)
% 7.47/7.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.47/7.69             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 7.47/7.69       ((v3_pre_topc @ sk_B @ sk_A))),
% 7.47/7.69      inference('sup-', [status(thm)], ['113', '114'])).
% 7.47/7.69  thf('116', plain, ($false),
% 7.47/7.69      inference('sat_resolution*', [status(thm)], ['1', '38', '39', '115'])).
% 7.47/7.69  
% 7.47/7.69  % SZS output end Refutation
% 7.47/7.69  
% 7.47/7.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
