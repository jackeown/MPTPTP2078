%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ge42oL9yss

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:22 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 239 expanded)
%              Number of leaves         :   42 (  87 expanded)
%              Depth                    :   13
%              Number of atoms          : 1226 (2632 expanded)
%              Number of equality atoms :   95 ( 185 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X66 ) ) )
      | ( ( k1_tops_1 @ X66 @ X65 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X66 ) @ X65 @ ( k2_tops_1 @ X66 @ X65 ) ) )
      | ~ ( l1_pre_topc @ X66 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X40 @ X42 )
        = ( k4_xboole_0 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X40 @ X42 )
        = ( k6_subset_1 @ X40 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k6_subset_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('20',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ~ ( v3_pre_topc @ X60 @ X61 )
      | ~ ( r1_tarski @ X60 @ X62 )
      | ( r1_tarski @ X60 @ ( k1_tops_1 @ X61 @ X62 ) )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_tarski @ sk_B_1 @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('33',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( ( k2_tops_1 @ X59 @ X58 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X59 ) @ ( k2_pre_topc @ X59 @ X58 ) @ ( k1_tops_1 @ X59 @ X58 ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('43',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( l1_pre_topc @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X52 @ X53 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X40 @ X42 )
        = ( k6_subset_1 @ X40 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('51',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('56',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('57',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('58',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('59',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('60',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X19 @ ( k6_subset_1 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('62',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('63',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k6_subset_1 @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ X0 ) @ ( k5_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','66'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('68',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('69',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('73',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('78',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('79',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('80',plain,(
    ! [X16: $i] :
      ( ( k6_subset_1 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','72','77','80'])).

thf('82',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['50','81'])).

thf('83',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('84',plain,
    ( ( ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('85',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('86',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X16: $i] :
      ( ( k6_subset_1 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['84','89'])).

thf('91',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf('92',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('94',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( l1_pre_topc @ X56 )
      | ~ ( v2_pre_topc @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X56 @ X57 ) @ X56 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('95',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['92','98'])).

thf('100',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','40','41','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ge42oL9yss
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:03:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.84/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.03  % Solved by: fo/fo7.sh
% 0.84/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.03  % done 1103 iterations in 0.574s
% 0.84/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.03  % SZS output start Refutation
% 0.84/1.03  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.84/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.84/1.03  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.84/1.03  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.84/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.03  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.84/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.84/1.03  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.84/1.03  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.84/1.03  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.84/1.03  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.84/1.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.84/1.03  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.84/1.03  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.84/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.84/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.84/1.03  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.84/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.03  thf(t76_tops_1, conjecture,
% 0.84/1.03    (![A:$i]:
% 0.84/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.03       ( ![B:$i]:
% 0.84/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.03           ( ( v3_pre_topc @ B @ A ) <=>
% 0.84/1.03             ( ( k2_tops_1 @ A @ B ) =
% 0.84/1.03               ( k7_subset_1 @
% 0.84/1.03                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.84/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.03    (~( ![A:$i]:
% 0.84/1.03        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.03          ( ![B:$i]:
% 0.84/1.03            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.03              ( ( v3_pre_topc @ B @ A ) <=>
% 0.84/1.03                ( ( k2_tops_1 @ A @ B ) =
% 0.84/1.03                  ( k7_subset_1 @
% 0.84/1.03                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.84/1.03    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.84/1.03  thf('0', plain,
% 0.84/1.03      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 0.84/1.03        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('1', plain,
% 0.84/1.03      (~
% 0.84/1.03       (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 0.84/1.03       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.84/1.03      inference('split', [status(esa)], ['0'])).
% 0.84/1.03  thf('2', plain,
% 0.84/1.03      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(t74_tops_1, axiom,
% 0.84/1.03    (![A:$i]:
% 0.84/1.03     ( ( l1_pre_topc @ A ) =>
% 0.84/1.03       ( ![B:$i]:
% 0.84/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.03           ( ( k1_tops_1 @ A @ B ) =
% 0.84/1.03             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.84/1.03  thf('3', plain,
% 0.84/1.03      (![X65 : $i, X66 : $i]:
% 0.84/1.03         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (u1_struct_0 @ X66)))
% 0.84/1.03          | ((k1_tops_1 @ X66 @ X65)
% 0.84/1.03              = (k7_subset_1 @ (u1_struct_0 @ X66) @ X65 @ 
% 0.84/1.03                 (k2_tops_1 @ X66 @ X65)))
% 0.84/1.03          | ~ (l1_pre_topc @ X66))),
% 0.84/1.03      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.84/1.03  thf('4', plain,
% 0.84/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.84/1.03        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.84/1.03               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.84/1.03      inference('sup-', [status(thm)], ['2', '3'])).
% 0.84/1.03  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('6', plain,
% 0.84/1.03      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(redefinition_k7_subset_1, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i]:
% 0.84/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.03       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.84/1.03  thf('7', plain,
% 0.84/1.03      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.84/1.03         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.84/1.03          | ((k7_subset_1 @ X41 @ X40 @ X42) = (k4_xboole_0 @ X40 @ X42)))),
% 0.84/1.03      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.84/1.03  thf(redefinition_k6_subset_1, axiom,
% 0.84/1.03    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.84/1.03  thf('8', plain,
% 0.84/1.03      (![X38 : $i, X39 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 0.84/1.03      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.03  thf('9', plain,
% 0.84/1.03      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.84/1.03         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.84/1.03          | ((k7_subset_1 @ X41 @ X40 @ X42) = (k6_subset_1 @ X40 @ X42)))),
% 0.84/1.03      inference('demod', [status(thm)], ['7', '8'])).
% 0.84/1.03  thf('10', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 0.84/1.03           = (k6_subset_1 @ sk_B_1 @ X0))),
% 0.84/1.03      inference('sup-', [status(thm)], ['6', '9'])).
% 0.84/1.03  thf('11', plain,
% 0.84/1.03      (((k1_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 0.84/1.03      inference('demod', [status(thm)], ['4', '5', '10'])).
% 0.84/1.03  thf(dt_k6_subset_1, axiom,
% 0.84/1.03    (![A:$i,B:$i]:
% 0.84/1.03     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.84/1.03  thf('12', plain,
% 0.84/1.03      (![X28 : $i, X29 : $i]:
% 0.84/1.03         (m1_subset_1 @ (k6_subset_1 @ X28 @ X29) @ (k1_zfmisc_1 @ X28))),
% 0.84/1.03      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.84/1.03  thf(t3_subset, axiom,
% 0.84/1.03    (![A:$i,B:$i]:
% 0.84/1.03     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.84/1.03  thf('13', plain,
% 0.84/1.03      (![X49 : $i, X50 : $i]:
% 0.84/1.03         ((r1_tarski @ X49 @ X50) | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50)))),
% 0.84/1.03      inference('cnf', [status(esa)], [t3_subset])).
% 0.84/1.03  thf('14', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.84/1.03      inference('sup-', [status(thm)], ['12', '13'])).
% 0.84/1.03  thf('15', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.84/1.03      inference('sup+', [status(thm)], ['11', '14'])).
% 0.84/1.03  thf('16', plain,
% 0.84/1.03      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('17', plain,
% 0.84/1.03      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 0.84/1.03        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('18', plain,
% 0.84/1.03      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.84/1.03      inference('split', [status(esa)], ['17'])).
% 0.84/1.03  thf('19', plain,
% 0.84/1.03      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(t56_tops_1, axiom,
% 0.84/1.03    (![A:$i]:
% 0.84/1.03     ( ( l1_pre_topc @ A ) =>
% 0.84/1.03       ( ![B:$i]:
% 0.84/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.03           ( ![C:$i]:
% 0.84/1.03             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.03               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.84/1.03                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.84/1.03  thf('20', plain,
% 0.84/1.03      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.84/1.03         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 0.84/1.03          | ~ (v3_pre_topc @ X60 @ X61)
% 0.84/1.03          | ~ (r1_tarski @ X60 @ X62)
% 0.84/1.03          | (r1_tarski @ X60 @ (k1_tops_1 @ X61 @ X62))
% 0.84/1.03          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 0.84/1.03          | ~ (l1_pre_topc @ X61))),
% 0.84/1.03      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.84/1.03  thf('21', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         (~ (l1_pre_topc @ sk_A)
% 0.84/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.03          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.84/1.03          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.84/1.03          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.84/1.03      inference('sup-', [status(thm)], ['19', '20'])).
% 0.84/1.03  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('23', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.03          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.84/1.03          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.84/1.03          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.84/1.03      inference('demod', [status(thm)], ['21', '22'])).
% 0.84/1.03  thf('24', plain,
% 0.84/1.03      ((![X0 : $i]:
% 0.84/1.03          (~ (r1_tarski @ sk_B_1 @ X0)
% 0.84/1.03           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.84/1.03           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.84/1.03         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.84/1.03      inference('sup-', [status(thm)], ['18', '23'])).
% 0.84/1.03  thf('25', plain,
% 0.84/1.03      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.84/1.03         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 0.84/1.03         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.84/1.03      inference('sup-', [status(thm)], ['16', '24'])).
% 0.84/1.03  thf(d10_xboole_0, axiom,
% 0.84/1.03    (![A:$i,B:$i]:
% 0.84/1.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.84/1.03  thf('26', plain,
% 0.84/1.03      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 0.84/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.84/1.03  thf('27', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.84/1.03      inference('simplify', [status(thm)], ['26'])).
% 0.84/1.03  thf('28', plain,
% 0.84/1.03      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 0.84/1.03         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.84/1.03      inference('demod', [status(thm)], ['25', '27'])).
% 0.84/1.03  thf('29', plain,
% 0.84/1.03      (![X9 : $i, X11 : $i]:
% 0.84/1.03         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 0.84/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.84/1.03  thf('30', plain,
% 0.84/1.03      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.84/1.03         | ((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1))))
% 0.84/1.03         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.84/1.03      inference('sup-', [status(thm)], ['28', '29'])).
% 0.84/1.03  thf('31', plain,
% 0.84/1.03      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.84/1.03         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.84/1.03      inference('sup-', [status(thm)], ['15', '30'])).
% 0.84/1.03  thf('32', plain,
% 0.84/1.03      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(l78_tops_1, axiom,
% 0.84/1.03    (![A:$i]:
% 0.84/1.03     ( ( l1_pre_topc @ A ) =>
% 0.84/1.03       ( ![B:$i]:
% 0.84/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.03           ( ( k2_tops_1 @ A @ B ) =
% 0.84/1.03             ( k7_subset_1 @
% 0.84/1.03               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.84/1.03               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.84/1.03  thf('33', plain,
% 0.84/1.03      (![X58 : $i, X59 : $i]:
% 0.84/1.03         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 0.84/1.03          | ((k2_tops_1 @ X59 @ X58)
% 0.84/1.03              = (k7_subset_1 @ (u1_struct_0 @ X59) @ 
% 0.84/1.03                 (k2_pre_topc @ X59 @ X58) @ (k1_tops_1 @ X59 @ X58)))
% 0.84/1.03          | ~ (l1_pre_topc @ X59))),
% 0.84/1.03      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.84/1.03  thf('34', plain,
% 0.84/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.84/1.03        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 0.84/1.03      inference('sup-', [status(thm)], ['32', '33'])).
% 0.84/1.03  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('36', plain,
% 0.84/1.03      (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.84/1.03      inference('demod', [status(thm)], ['34', '35'])).
% 0.84/1.03  thf('37', plain,
% 0.84/1.03      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.84/1.03         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.84/1.03      inference('sup+', [status(thm)], ['31', '36'])).
% 0.84/1.03  thf('38', plain,
% 0.84/1.03      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.84/1.03         <= (~
% 0.84/1.03             (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.84/1.03      inference('split', [status(esa)], ['0'])).
% 0.84/1.03  thf('39', plain,
% 0.84/1.03      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 0.84/1.03         <= (~
% 0.84/1.03             (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 0.84/1.03             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.84/1.03      inference('sup-', [status(thm)], ['37', '38'])).
% 0.84/1.03  thf('40', plain,
% 0.84/1.03      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 0.84/1.03       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.84/1.03      inference('simplify', [status(thm)], ['39'])).
% 0.84/1.03  thf('41', plain,
% 0.84/1.03      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 0.84/1.03       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.84/1.03      inference('split', [status(esa)], ['17'])).
% 0.84/1.03  thf('42', plain,
% 0.84/1.03      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(dt_k2_pre_topc, axiom,
% 0.84/1.03    (![A:$i,B:$i]:
% 0.84/1.03     ( ( ( l1_pre_topc @ A ) & 
% 0.84/1.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.84/1.03       ( m1_subset_1 @
% 0.84/1.03         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.84/1.03  thf('43', plain,
% 0.84/1.03      (![X52 : $i, X53 : $i]:
% 0.84/1.03         (~ (l1_pre_topc @ X52)
% 0.84/1.03          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.84/1.03          | (m1_subset_1 @ (k2_pre_topc @ X52 @ X53) @ 
% 0.84/1.03             (k1_zfmisc_1 @ (u1_struct_0 @ X52))))),
% 0.84/1.03      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.84/1.03  thf('44', plain,
% 0.84/1.03      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.84/1.03         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.03        | ~ (l1_pre_topc @ sk_A))),
% 0.84/1.03      inference('sup-', [status(thm)], ['42', '43'])).
% 0.84/1.03  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('46', plain,
% 0.84/1.03      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.84/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('demod', [status(thm)], ['44', '45'])).
% 0.84/1.03  thf('47', plain,
% 0.84/1.03      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.84/1.03         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 0.84/1.03          | ((k7_subset_1 @ X41 @ X40 @ X42) = (k6_subset_1 @ X40 @ X42)))),
% 0.84/1.03      inference('demod', [status(thm)], ['7', '8'])).
% 0.84/1.03  thf('48', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 0.84/1.03           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 0.84/1.03      inference('sup-', [status(thm)], ['46', '47'])).
% 0.84/1.03  thf('49', plain,
% 0.84/1.03      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.84/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.84/1.03      inference('split', [status(esa)], ['17'])).
% 0.84/1.03  thf('50', plain,
% 0.84/1.03      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.84/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.84/1.03      inference('sup+', [status(thm)], ['48', '49'])).
% 0.84/1.03  thf(idempotence_k3_xboole_0, axiom,
% 0.84/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.84/1.03  thf('51', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 0.84/1.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.84/1.03  thf(t100_xboole_1, axiom,
% 0.84/1.03    (![A:$i,B:$i]:
% 0.84/1.03     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.84/1.03  thf('52', plain,
% 0.84/1.03      (![X12 : $i, X13 : $i]:
% 0.84/1.03         ((k4_xboole_0 @ X12 @ X13)
% 0.84/1.03           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.84/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.84/1.03  thf('53', plain,
% 0.84/1.03      (![X38 : $i, X39 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 0.84/1.03      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.03  thf('54', plain,
% 0.84/1.03      (![X12 : $i, X13 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X12 @ X13)
% 0.84/1.03           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.84/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.84/1.03  thf('55', plain,
% 0.84/1.03      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.84/1.03      inference('sup+', [status(thm)], ['51', '54'])).
% 0.84/1.03  thf(t52_xboole_1, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i]:
% 0.84/1.03     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.84/1.03       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.84/1.03  thf('56', plain,
% 0.84/1.03      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.84/1.03         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.84/1.03           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 0.84/1.03              (k3_xboole_0 @ X19 @ X21)))),
% 0.84/1.03      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.84/1.03  thf('57', plain,
% 0.84/1.03      (![X38 : $i, X39 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 0.84/1.03      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.03  thf('58', plain,
% 0.84/1.03      (![X38 : $i, X39 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 0.84/1.03      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.03  thf('59', plain,
% 0.84/1.03      (![X38 : $i, X39 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 0.84/1.03      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.03  thf('60', plain,
% 0.84/1.03      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X19 @ (k6_subset_1 @ X20 @ X21))
% 0.84/1.03           = (k2_xboole_0 @ (k6_subset_1 @ X19 @ X20) @ 
% 0.84/1.03              (k3_xboole_0 @ X19 @ X21)))),
% 0.84/1.03      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.84/1.03  thf(commutativity_k2_xboole_0, axiom,
% 0.84/1.03    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.84/1.03  thf('61', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.84/1.03      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.84/1.03  thf(t46_xboole_1, axiom,
% 0.84/1.03    (![A:$i,B:$i]:
% 0.84/1.03     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.84/1.03  thf('62', plain,
% 0.84/1.03      (![X17 : $i, X18 : $i]:
% 0.84/1.03         ((k4_xboole_0 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (k1_xboole_0))),
% 0.84/1.03      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.84/1.03  thf('63', plain,
% 0.84/1.03      (![X38 : $i, X39 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 0.84/1.03      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.03  thf('64', plain,
% 0.84/1.03      (![X17 : $i, X18 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (k1_xboole_0))),
% 0.84/1.03      inference('demod', [status(thm)], ['62', '63'])).
% 0.84/1.03  thf('65', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.84/1.03      inference('sup+', [status(thm)], ['61', '64'])).
% 0.84/1.03  thf('66', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.03         ((k6_subset_1 @ (k3_xboole_0 @ X2 @ X0) @ 
% 0.84/1.03           (k6_subset_1 @ X2 @ (k6_subset_1 @ X1 @ X0))) = (k1_xboole_0))),
% 0.84/1.03      inference('sup+', [status(thm)], ['60', '65'])).
% 0.84/1.03  thf('67', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]:
% 0.84/1.03         ((k6_subset_1 @ (k3_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ X0) @ 
% 0.84/1.03           (k5_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))
% 0.84/1.03           = (k1_xboole_0))),
% 0.84/1.03      inference('sup+', [status(thm)], ['55', '66'])).
% 0.84/1.03  thf(commutativity_k2_tarski, axiom,
% 0.84/1.03    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.84/1.03  thf('68', plain,
% 0.84/1.03      (![X22 : $i, X23 : $i]:
% 0.84/1.03         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 0.84/1.03      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.84/1.03  thf(t12_setfam_1, axiom,
% 0.84/1.03    (![A:$i,B:$i]:
% 0.84/1.03     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.84/1.03  thf('69', plain,
% 0.84/1.03      (![X47 : $i, X48 : $i]:
% 0.84/1.03         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 0.84/1.03      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.84/1.03  thf('70', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]:
% 0.84/1.03         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.03      inference('sup+', [status(thm)], ['68', '69'])).
% 0.84/1.03  thf('71', plain,
% 0.84/1.03      (![X47 : $i, X48 : $i]:
% 0.84/1.03         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 0.84/1.03      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.84/1.03  thf('72', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.03      inference('sup+', [status(thm)], ['70', '71'])).
% 0.84/1.03  thf(t1_boole, axiom,
% 0.84/1.03    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.84/1.03  thf('73', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.84/1.03      inference('cnf', [status(esa)], [t1_boole])).
% 0.84/1.03  thf('74', plain,
% 0.84/1.03      (![X17 : $i, X18 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X17 @ (k2_xboole_0 @ X17 @ X18)) = (k1_xboole_0))),
% 0.84/1.03      inference('demod', [status(thm)], ['62', '63'])).
% 0.84/1.03  thf('75', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.84/1.03      inference('sup+', [status(thm)], ['73', '74'])).
% 0.84/1.03  thf('76', plain,
% 0.84/1.03      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.84/1.03      inference('sup+', [status(thm)], ['51', '54'])).
% 0.84/1.03  thf('77', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.84/1.03      inference('demod', [status(thm)], ['75', '76'])).
% 0.84/1.03  thf(t3_boole, axiom,
% 0.84/1.03    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.84/1.03  thf('78', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.84/1.03      inference('cnf', [status(esa)], [t3_boole])).
% 0.84/1.03  thf('79', plain,
% 0.84/1.03      (![X38 : $i, X39 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 0.84/1.03      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.03  thf('80', plain, (![X16 : $i]: ((k6_subset_1 @ X16 @ k1_xboole_0) = (X16))),
% 0.84/1.03      inference('demod', [status(thm)], ['78', '79'])).
% 0.84/1.03  thf('81', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]:
% 0.84/1.03         ((k3_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)) = (k1_xboole_0))),
% 0.84/1.03      inference('demod', [status(thm)], ['67', '72', '77', '80'])).
% 0.84/1.03  thf('82', plain,
% 0.84/1.03      ((((k3_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 0.84/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.84/1.03      inference('sup+', [status(thm)], ['50', '81'])).
% 0.84/1.03  thf('83', plain,
% 0.84/1.03      (![X12 : $i, X13 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X12 @ X13)
% 0.84/1.03           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.84/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.84/1.03  thf('84', plain,
% 0.84/1.03      ((((k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))
% 0.84/1.03          = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0)))
% 0.84/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.84/1.03      inference('sup+', [status(thm)], ['82', '83'])).
% 0.84/1.03  thf(t2_boole, axiom,
% 0.84/1.03    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.84/1.03  thf('85', plain,
% 0.84/1.03      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.84/1.03      inference('cnf', [status(esa)], [t2_boole])).
% 0.84/1.03  thf('86', plain,
% 0.84/1.03      (![X12 : $i, X13 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X12 @ X13)
% 0.84/1.03           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.84/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.84/1.03  thf('87', plain,
% 0.84/1.03      (![X0 : $i]:
% 0.84/1.03         ((k6_subset_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.84/1.03      inference('sup+', [status(thm)], ['85', '86'])).
% 0.84/1.03  thf('88', plain, (![X16 : $i]: ((k6_subset_1 @ X16 @ k1_xboole_0) = (X16))),
% 0.84/1.03      inference('demod', [status(thm)], ['78', '79'])).
% 0.84/1.03  thf('89', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.84/1.03      inference('sup+', [status(thm)], ['87', '88'])).
% 0.84/1.03  thf('90', plain,
% 0.84/1.03      ((((k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.84/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.84/1.03      inference('demod', [status(thm)], ['84', '89'])).
% 0.84/1.03  thf('91', plain,
% 0.84/1.03      (((k1_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 0.84/1.03      inference('demod', [status(thm)], ['4', '5', '10'])).
% 0.84/1.03  thf('92', plain,
% 0.84/1.03      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.84/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.84/1.03      inference('sup+', [status(thm)], ['90', '91'])).
% 0.84/1.03  thf('93', plain,
% 0.84/1.03      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(fc9_tops_1, axiom,
% 0.84/1.03    (![A:$i,B:$i]:
% 0.84/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.84/1.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.84/1.03       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.84/1.03  thf('94', plain,
% 0.84/1.03      (![X56 : $i, X57 : $i]:
% 0.84/1.03         (~ (l1_pre_topc @ X56)
% 0.84/1.03          | ~ (v2_pre_topc @ X56)
% 0.84/1.03          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 0.84/1.03          | (v3_pre_topc @ (k1_tops_1 @ X56 @ X57) @ X56))),
% 0.84/1.03      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.84/1.03  thf('95', plain,
% 0.84/1.03      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.84/1.03        | ~ (v2_pre_topc @ sk_A)
% 0.84/1.03        | ~ (l1_pre_topc @ sk_A))),
% 0.84/1.03      inference('sup-', [status(thm)], ['93', '94'])).
% 0.84/1.03  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf('98', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.84/1.03      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.84/1.03  thf('99', plain,
% 0.84/1.03      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 0.84/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.84/1.03      inference('sup+', [status(thm)], ['92', '98'])).
% 0.84/1.03  thf('100', plain,
% 0.84/1.03      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.84/1.03      inference('split', [status(esa)], ['0'])).
% 0.84/1.03  thf('101', plain,
% 0.84/1.03      (~
% 0.84/1.03       (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.84/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.84/1.03             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 0.84/1.03       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.84/1.03      inference('sup-', [status(thm)], ['99', '100'])).
% 0.84/1.03  thf('102', plain, ($false),
% 0.84/1.03      inference('sat_resolution*', [status(thm)], ['1', '40', '41', '101'])).
% 0.84/1.03  
% 0.84/1.03  % SZS output end Refutation
% 0.84/1.03  
% 0.84/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
