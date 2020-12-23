%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.djlj92pUAr

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:22 EST 2020

% Result     : Theorem 24.30s
% Output     : Refutation 24.30s
% Verified   : 
% Statistics : Number of formulae       :  302 (4011 expanded)
%              Number of leaves         :   51 (1337 expanded)
%              Depth                    :   28
%              Number of atoms          : 2732 (34324 expanded)
%              Number of equality atoms :  206 (2889 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

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

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ~ ( v3_pre_topc @ X58 @ X59 )
      | ~ ( r1_tarski @ X58 @ X60 )
      | ( r1_tarski @ X58 @ ( k1_tops_1 @ X59 @ X60 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_tarski @ sk_B_1 @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X66 ) ) )
      | ( ( k1_tops_1 @ X66 @ X65 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X66 ) @ X65 @ ( k2_tops_1 @ X66 @ X65 ) ) )
      | ~ ( l1_pre_topc @ X66 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k7_subset_1 @ X40 @ X39 @ X41 )
        = ( k4_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('23',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k7_subset_1 @ X40 @ X39 @ X41 )
        = ( k6_subset_1 @ X39 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k6_subset_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X26: $i,X27: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('36',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( ( k2_tops_1 @ X57 @ X56 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X57 ) @ ( k2_pre_topc @ X57 @ X56 ) @ ( k1_tops_1 @ X57 @ X56 ) ) )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( l1_pre_topc @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X50 @ X51 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k7_subset_1 @ X40 @ X39 @ X41 )
        = ( k6_subset_1 @ X39 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['39','46'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('56',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('59',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      = ( k2_pre_topc @ sk_A @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['57','61'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('63',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('64',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
      = ( k2_pre_topc @ sk_A @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('70',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('71',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('75',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k7_subset_1 @ X43 @ X44 @ X42 )
        = ( k9_subset_1 @ X43 @ X44 @ ( k3_subset_1 @ X43 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ X1 )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('78',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('79',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('80',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k6_subset_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ X1 )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ X1 )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['73','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('85',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k7_subset_1 @ X40 @ X39 @ X41 )
        = ( k6_subset_1 @ X39 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ X2 )
      = ( k6_subset_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('89',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X33 @ ( k3_subset_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('92',plain,(
    ! [X26: $i,X27: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('93',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k6_subset_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['90','91','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('97',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('98',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('99',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('102',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('105',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','110'])).

thf('112',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('116',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('117',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k6_subset_1 @ X37 @ X38 )
      = ( k4_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('118',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','110'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('126',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['95','128'])).

thf('130',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('135',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['87','137'])).

thf('139',plain,
    ( ( ( k6_subset_1 @ ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['68','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X33 @ ( k3_subset_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('142',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k6_subset_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('145',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['142','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('148',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('150',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('152',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('153',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['149','154'])).

thf('156',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('157',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('159',plain,
    ( ( k6_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('161',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('163',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('165',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['148','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('168',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( l1_pre_topc @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X52 @ X53 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('169',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X26: $i,X27: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('173',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k2_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['171','174'])).

thf('176',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['166','175'])).

thf('177',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('178',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ( ( k2_pre_topc @ X64 @ X63 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X64 ) @ X63 @ ( k2_tops_1 @ X64 @ X63 ) ) )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('179',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['148','165'])).

thf('183',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['176','181','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('185',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('187',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['183','184'])).

thf('188',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['183','184'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('190',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['176','181','182'])).

thf('191',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['176','181','182'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','136'])).

thf('193',plain,
    ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['176','181','182'])).

thf('195',plain,
    ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('197',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('199',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','136'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X33 @ ( k3_subset_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['202','203'])).

thf('208',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k6_subset_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['206','209','210'])).

thf('212',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['95','128'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['212','215'])).

thf('217',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['218','219','220'])).

thf('222',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['211','225'])).

thf('227',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['201','226','227'])).

thf('229',plain,
    ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['198','228'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('231',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['183','184'])).

thf('232',plain,
    ( sk_B_1
    = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,
    ( ( sk_B_1
      = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['197','232'])).

thf('234',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('235',plain,(
    ! [X47: $i,X49: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( r1_tarski @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('236',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('237',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k9_subset_1 @ X30 @ X29 @ X29 )
        = X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['139','185','186','187','188','189','190','233','238'])).

thf('240',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('241',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( l1_pre_topc @ X54 )
      | ~ ( v2_pre_topc @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X54 @ X55 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('242',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('246',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['239','245'])).

thf('247',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('248',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','53','54','248'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.djlj92pUAr
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:19:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 24.30/24.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 24.30/24.48  % Solved by: fo/fo7.sh
% 24.30/24.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 24.30/24.48  % done 35702 iterations in 24.025s
% 24.30/24.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 24.30/24.48  % SZS output start Refutation
% 24.30/24.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 24.30/24.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 24.30/24.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 24.30/24.48  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 24.30/24.48  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 24.30/24.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 24.30/24.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 24.30/24.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 24.30/24.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 24.30/24.48  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 24.30/24.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 24.30/24.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 24.30/24.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 24.30/24.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 24.30/24.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 24.30/24.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 24.30/24.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 24.30/24.48  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 24.30/24.48  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 24.30/24.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 24.30/24.48  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 24.30/24.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 24.30/24.48  thf(sk_A_type, type, sk_A: $i).
% 24.30/24.48  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 24.30/24.48  thf(t76_tops_1, conjecture,
% 24.30/24.48    (![A:$i]:
% 24.30/24.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 24.30/24.48       ( ![B:$i]:
% 24.30/24.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.30/24.48           ( ( v3_pre_topc @ B @ A ) <=>
% 24.30/24.48             ( ( k2_tops_1 @ A @ B ) =
% 24.30/24.48               ( k7_subset_1 @
% 24.30/24.48                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 24.30/24.48  thf(zf_stmt_0, negated_conjecture,
% 24.30/24.48    (~( ![A:$i]:
% 24.30/24.48        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 24.30/24.48          ( ![B:$i]:
% 24.30/24.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.30/24.48              ( ( v3_pre_topc @ B @ A ) <=>
% 24.30/24.48                ( ( k2_tops_1 @ A @ B ) =
% 24.30/24.48                  ( k7_subset_1 @
% 24.30/24.48                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 24.30/24.48    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 24.30/24.48  thf('0', plain,
% 24.30/24.48      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 24.30/24.48        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf('1', plain,
% 24.30/24.48      (~
% 24.30/24.48       (((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 24.30/24.48       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 24.30/24.48      inference('split', [status(esa)], ['0'])).
% 24.30/24.48  thf('2', plain,
% 24.30/24.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf('3', plain,
% 24.30/24.48      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 24.30/24.48        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf('4', plain,
% 24.30/24.48      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 24.30/24.48      inference('split', [status(esa)], ['3'])).
% 24.30/24.48  thf('5', plain,
% 24.30/24.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf(t56_tops_1, axiom,
% 24.30/24.48    (![A:$i]:
% 24.30/24.48     ( ( l1_pre_topc @ A ) =>
% 24.30/24.48       ( ![B:$i]:
% 24.30/24.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.30/24.48           ( ![C:$i]:
% 24.30/24.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.30/24.48               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 24.30/24.48                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 24.30/24.48  thf('6', plain,
% 24.30/24.48      (![X58 : $i, X59 : $i, X60 : $i]:
% 24.30/24.48         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 24.30/24.48          | ~ (v3_pre_topc @ X58 @ X59)
% 24.30/24.48          | ~ (r1_tarski @ X58 @ X60)
% 24.30/24.48          | (r1_tarski @ X58 @ (k1_tops_1 @ X59 @ X60))
% 24.30/24.48          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 24.30/24.48          | ~ (l1_pre_topc @ X59))),
% 24.30/24.48      inference('cnf', [status(esa)], [t56_tops_1])).
% 24.30/24.48  thf('7', plain,
% 24.30/24.48      (![X0 : $i]:
% 24.30/24.48         (~ (l1_pre_topc @ sk_A)
% 24.30/24.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 24.30/24.48          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 24.30/24.48          | ~ (r1_tarski @ sk_B_1 @ X0)
% 24.30/24.48          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 24.30/24.48      inference('sup-', [status(thm)], ['5', '6'])).
% 24.30/24.48  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf('9', plain,
% 24.30/24.48      (![X0 : $i]:
% 24.30/24.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 24.30/24.48          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 24.30/24.48          | ~ (r1_tarski @ sk_B_1 @ X0)
% 24.30/24.48          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 24.30/24.48      inference('demod', [status(thm)], ['7', '8'])).
% 24.30/24.48  thf('10', plain,
% 24.30/24.48      ((![X0 : $i]:
% 24.30/24.48          (~ (r1_tarski @ sk_B_1 @ X0)
% 24.30/24.48           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 24.30/24.48           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 24.30/24.48         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['4', '9'])).
% 24.30/24.48  thf('11', plain,
% 24.30/24.48      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 24.30/24.48         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 24.30/24.48         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['2', '10'])).
% 24.30/24.48  thf(d10_xboole_0, axiom,
% 24.30/24.48    (![A:$i,B:$i]:
% 24.30/24.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 24.30/24.48  thf('12', plain,
% 24.30/24.48      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 24.30/24.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 24.30/24.48  thf('13', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 24.30/24.48      inference('simplify', [status(thm)], ['12'])).
% 24.30/24.48  thf('14', plain,
% 24.30/24.48      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 24.30/24.48         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 24.30/24.48      inference('demod', [status(thm)], ['11', '13'])).
% 24.30/24.48  thf('15', plain,
% 24.30/24.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf(t74_tops_1, axiom,
% 24.30/24.48    (![A:$i]:
% 24.30/24.48     ( ( l1_pre_topc @ A ) =>
% 24.30/24.48       ( ![B:$i]:
% 24.30/24.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.30/24.48           ( ( k1_tops_1 @ A @ B ) =
% 24.30/24.48             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 24.30/24.48  thf('16', plain,
% 24.30/24.48      (![X65 : $i, X66 : $i]:
% 24.30/24.48         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (u1_struct_0 @ X66)))
% 24.30/24.48          | ((k1_tops_1 @ X66 @ X65)
% 24.30/24.48              = (k7_subset_1 @ (u1_struct_0 @ X66) @ X65 @ 
% 24.30/24.48                 (k2_tops_1 @ X66 @ X65)))
% 24.30/24.48          | ~ (l1_pre_topc @ X66))),
% 24.30/24.48      inference('cnf', [status(esa)], [t74_tops_1])).
% 24.30/24.48  thf('17', plain,
% 24.30/24.48      ((~ (l1_pre_topc @ sk_A)
% 24.30/24.48        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 24.30/24.48               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 24.30/24.48      inference('sup-', [status(thm)], ['15', '16'])).
% 24.30/24.48  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf('19', plain,
% 24.30/24.48      (((k1_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 24.30/24.48            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['17', '18'])).
% 24.30/24.48  thf('20', plain,
% 24.30/24.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf(redefinition_k7_subset_1, axiom,
% 24.30/24.48    (![A:$i,B:$i,C:$i]:
% 24.30/24.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 24.30/24.48       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 24.30/24.48  thf('21', plain,
% 24.30/24.48      (![X39 : $i, X40 : $i, X41 : $i]:
% 24.30/24.48         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 24.30/24.48          | ((k7_subset_1 @ X40 @ X39 @ X41) = (k4_xboole_0 @ X39 @ X41)))),
% 24.30/24.48      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 24.30/24.48  thf(redefinition_k6_subset_1, axiom,
% 24.30/24.48    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 24.30/24.48  thf('22', plain,
% 24.30/24.48      (![X37 : $i, X38 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 24.30/24.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 24.30/24.48  thf('23', plain,
% 24.30/24.48      (![X39 : $i, X40 : $i, X41 : $i]:
% 24.30/24.48         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 24.30/24.48          | ((k7_subset_1 @ X40 @ X39 @ X41) = (k6_subset_1 @ X39 @ X41)))),
% 24.30/24.48      inference('demod', [status(thm)], ['21', '22'])).
% 24.30/24.48  thf('24', plain,
% 24.30/24.48      (![X0 : $i]:
% 24.30/24.48         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 24.30/24.48           = (k6_subset_1 @ sk_B_1 @ X0))),
% 24.30/24.48      inference('sup-', [status(thm)], ['20', '23'])).
% 24.30/24.48  thf('25', plain,
% 24.30/24.48      (((k1_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['19', '24'])).
% 24.30/24.48  thf(dt_k6_subset_1, axiom,
% 24.30/24.48    (![A:$i,B:$i]:
% 24.30/24.48     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 24.30/24.48  thf('26', plain,
% 24.30/24.48      (![X26 : $i, X27 : $i]:
% 24.30/24.48         (m1_subset_1 @ (k6_subset_1 @ X26 @ X27) @ (k1_zfmisc_1 @ X26))),
% 24.30/24.48      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 24.30/24.48  thf(t3_subset, axiom,
% 24.30/24.48    (![A:$i,B:$i]:
% 24.30/24.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 24.30/24.48  thf('27', plain,
% 24.30/24.48      (![X47 : $i, X48 : $i]:
% 24.30/24.48         ((r1_tarski @ X47 @ X48) | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48)))),
% 24.30/24.48      inference('cnf', [status(esa)], [t3_subset])).
% 24.30/24.48  thf('28', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 24.30/24.48      inference('sup-', [status(thm)], ['26', '27'])).
% 24.30/24.48  thf('29', plain,
% 24.30/24.48      (![X2 : $i, X4 : $i]:
% 24.30/24.48         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 24.30/24.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 24.30/24.48  thf('30', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 24.30/24.48          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['28', '29'])).
% 24.30/24.48  thf('31', plain,
% 24.30/24.48      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 24.30/24.48        | ((sk_B_1) = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 24.30/24.48      inference('sup-', [status(thm)], ['25', '30'])).
% 24.30/24.48  thf('32', plain,
% 24.30/24.48      (((k1_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['19', '24'])).
% 24.30/24.48  thf('33', plain,
% 24.30/24.48      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 24.30/24.48        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['31', '32'])).
% 24.30/24.48  thf('34', plain,
% 24.30/24.48      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 24.30/24.48         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['14', '33'])).
% 24.30/24.48  thf('35', plain,
% 24.30/24.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf(l78_tops_1, axiom,
% 24.30/24.48    (![A:$i]:
% 24.30/24.48     ( ( l1_pre_topc @ A ) =>
% 24.30/24.48       ( ![B:$i]:
% 24.30/24.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.30/24.48           ( ( k2_tops_1 @ A @ B ) =
% 24.30/24.48             ( k7_subset_1 @
% 24.30/24.48               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 24.30/24.48               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 24.30/24.48  thf('36', plain,
% 24.30/24.48      (![X56 : $i, X57 : $i]:
% 24.30/24.48         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 24.30/24.48          | ((k2_tops_1 @ X57 @ X56)
% 24.30/24.48              = (k7_subset_1 @ (u1_struct_0 @ X57) @ 
% 24.30/24.48                 (k2_pre_topc @ X57 @ X56) @ (k1_tops_1 @ X57 @ X56)))
% 24.30/24.48          | ~ (l1_pre_topc @ X57))),
% 24.30/24.48      inference('cnf', [status(esa)], [l78_tops_1])).
% 24.30/24.48  thf('37', plain,
% 24.30/24.48      ((~ (l1_pre_topc @ sk_A)
% 24.30/24.48        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 24.30/24.48      inference('sup-', [status(thm)], ['35', '36'])).
% 24.30/24.48  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf('39', plain,
% 24.30/24.48      (((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['37', '38'])).
% 24.30/24.48  thf('40', plain,
% 24.30/24.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf(dt_k2_pre_topc, axiom,
% 24.30/24.48    (![A:$i,B:$i]:
% 24.30/24.48     ( ( ( l1_pre_topc @ A ) & 
% 24.30/24.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 24.30/24.48       ( m1_subset_1 @
% 24.30/24.48         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 24.30/24.48  thf('41', plain,
% 24.30/24.48      (![X50 : $i, X51 : $i]:
% 24.30/24.48         (~ (l1_pre_topc @ X50)
% 24.30/24.48          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 24.30/24.48          | (m1_subset_1 @ (k2_pre_topc @ X50 @ X51) @ 
% 24.30/24.48             (k1_zfmisc_1 @ (u1_struct_0 @ X50))))),
% 24.30/24.48      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 24.30/24.48  thf('42', plain,
% 24.30/24.48      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 24.30/24.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 24.30/24.48        | ~ (l1_pre_topc @ sk_A))),
% 24.30/24.48      inference('sup-', [status(thm)], ['40', '41'])).
% 24.30/24.48  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf('44', plain,
% 24.30/24.48      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 24.30/24.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.30/24.48      inference('demod', [status(thm)], ['42', '43'])).
% 24.30/24.48  thf('45', plain,
% 24.30/24.48      (![X39 : $i, X40 : $i, X41 : $i]:
% 24.30/24.48         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 24.30/24.48          | ((k7_subset_1 @ X40 @ X39 @ X41) = (k6_subset_1 @ X39 @ X41)))),
% 24.30/24.48      inference('demod', [status(thm)], ['21', '22'])).
% 24.30/24.48  thf('46', plain,
% 24.30/24.48      (![X0 : $i]:
% 24.30/24.48         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 24.30/24.48           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 24.30/24.48      inference('sup-', [status(thm)], ['44', '45'])).
% 24.30/24.48  thf('47', plain,
% 24.30/24.48      (((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 24.30/24.48            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['39', '46'])).
% 24.30/24.48  thf('48', plain,
% 24.30/24.48      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 24.30/24.48         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 24.30/24.48      inference('sup+', [status(thm)], ['34', '47'])).
% 24.30/24.48  thf('49', plain,
% 24.30/24.48      (![X0 : $i]:
% 24.30/24.48         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 24.30/24.48           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 24.30/24.48      inference('sup-', [status(thm)], ['44', '45'])).
% 24.30/24.48  thf('50', plain,
% 24.30/24.48      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 24.30/24.48         <= (~
% 24.30/24.48             (((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 24.30/24.48      inference('split', [status(esa)], ['0'])).
% 24.30/24.48  thf('51', plain,
% 24.30/24.48      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48          != (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 24.30/24.48         <= (~
% 24.30/24.48             (((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 24.30/24.48      inference('sup-', [status(thm)], ['49', '50'])).
% 24.30/24.48  thf('52', plain,
% 24.30/24.48      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 24.30/24.48         <= (~
% 24.30/24.48             (((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 24.30/24.48             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['48', '51'])).
% 24.30/24.48  thf('53', plain,
% 24.30/24.48      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 24.30/24.48       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 24.30/24.48      inference('simplify', [status(thm)], ['52'])).
% 24.30/24.48  thf('54', plain,
% 24.30/24.48      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 24.30/24.48       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 24.30/24.48      inference('split', [status(esa)], ['3'])).
% 24.30/24.48  thf('55', plain,
% 24.30/24.48      (![X0 : $i]:
% 24.30/24.48         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 24.30/24.48           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 24.30/24.48      inference('sup-', [status(thm)], ['44', '45'])).
% 24.30/24.48  thf('56', plain,
% 24.30/24.48      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 24.30/24.48         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 24.30/24.48      inference('split', [status(esa)], ['3'])).
% 24.30/24.48  thf('57', plain,
% 24.30/24.48      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 24.30/24.48         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 24.30/24.48      inference('sup+', [status(thm)], ['55', '56'])).
% 24.30/24.48  thf(t51_xboole_1, axiom,
% 24.30/24.48    (![A:$i,B:$i]:
% 24.30/24.48     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 24.30/24.48       ( A ) ))).
% 24.30/24.48  thf('58', plain,
% 24.30/24.48      (![X16 : $i, X17 : $i]:
% 24.30/24.48         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 24.30/24.48           = (X16))),
% 24.30/24.48      inference('cnf', [status(esa)], [t51_xboole_1])).
% 24.30/24.48  thf('59', plain,
% 24.30/24.48      (![X37 : $i, X38 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 24.30/24.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 24.30/24.48  thf(commutativity_k2_xboole_0, axiom,
% 24.30/24.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 24.30/24.48  thf('60', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 24.30/24.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 24.30/24.48  thf('61', plain,
% 24.30/24.48      (![X16 : $i, X17 : $i]:
% 24.30/24.48         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 24.30/24.48           = (X16))),
% 24.30/24.48      inference('demod', [status(thm)], ['58', '59', '60'])).
% 24.30/24.48  thf('62', plain,
% 24.30/24.48      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 24.30/24.48          (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 24.30/24.48          = (k2_pre_topc @ sk_A @ sk_B_1)))
% 24.30/24.48         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 24.30/24.48      inference('sup+', [status(thm)], ['57', '61'])).
% 24.30/24.48  thf(commutativity_k2_tarski, axiom,
% 24.30/24.48    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 24.30/24.48  thf('63', plain,
% 24.30/24.48      (![X20 : $i, X21 : $i]:
% 24.30/24.48         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 24.30/24.48      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 24.30/24.48  thf(t12_setfam_1, axiom,
% 24.30/24.48    (![A:$i,B:$i]:
% 24.30/24.48     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 24.30/24.48  thf('64', plain,
% 24.30/24.48      (![X45 : $i, X46 : $i]:
% 24.30/24.48         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 24.30/24.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 24.30/24.48  thf('65', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 24.30/24.48      inference('sup+', [status(thm)], ['63', '64'])).
% 24.30/24.48  thf('66', plain,
% 24.30/24.48      (![X45 : $i, X46 : $i]:
% 24.30/24.48         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 24.30/24.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 24.30/24.48  thf('67', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 24.30/24.48      inference('sup+', [status(thm)], ['65', '66'])).
% 24.30/24.48  thf('68', plain,
% 24.30/24.48      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 24.30/24.48          (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))
% 24.30/24.48          = (k2_pre_topc @ sk_A @ sk_B_1)))
% 24.30/24.48         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 24.30/24.48      inference('demod', [status(thm)], ['62', '67'])).
% 24.30/24.48  thf('69', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 24.30/24.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 24.30/24.48  thf(t7_xboole_1, axiom,
% 24.30/24.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 24.30/24.48  thf('70', plain,
% 24.30/24.48      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 24.30/24.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 24.30/24.48  thf('71', plain,
% 24.30/24.48      (![X47 : $i, X49 : $i]:
% 24.30/24.48         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 24.30/24.48      inference('cnf', [status(esa)], [t3_subset])).
% 24.30/24.48  thf('72', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['70', '71'])).
% 24.30/24.48  thf('73', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.30/24.48      inference('sup+', [status(thm)], ['69', '72'])).
% 24.30/24.48  thf('74', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['70', '71'])).
% 24.30/24.48  thf(t32_subset_1, axiom,
% 24.30/24.48    (![A:$i,B:$i]:
% 24.30/24.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 24.30/24.48       ( ![C:$i]:
% 24.30/24.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 24.30/24.48           ( ( k7_subset_1 @ A @ B @ C ) =
% 24.30/24.48             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 24.30/24.48  thf('75', plain,
% 24.30/24.48      (![X42 : $i, X43 : $i, X44 : $i]:
% 24.30/24.48         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 24.30/24.48          | ((k7_subset_1 @ X43 @ X44 @ X42)
% 24.30/24.48              = (k9_subset_1 @ X43 @ X44 @ (k3_subset_1 @ X43 @ X42)))
% 24.30/24.48          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X43)))),
% 24.30/24.48      inference('cnf', [status(esa)], [t32_subset_1])).
% 24.30/24.48  thf('76', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.30/24.48         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 24.30/24.48          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ X1)
% 24.30/24.48              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 24.30/24.48                 (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))))),
% 24.30/24.48      inference('sup-', [status(thm)], ['74', '75'])).
% 24.30/24.48  thf('77', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['70', '71'])).
% 24.30/24.48  thf(d5_subset_1, axiom,
% 24.30/24.48    (![A:$i,B:$i]:
% 24.30/24.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 24.30/24.48       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 24.30/24.48  thf('78', plain,
% 24.30/24.48      (![X22 : $i, X23 : $i]:
% 24.30/24.48         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 24.30/24.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 24.30/24.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 24.30/24.48  thf('79', plain,
% 24.30/24.48      (![X37 : $i, X38 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 24.30/24.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 24.30/24.48  thf('80', plain,
% 24.30/24.48      (![X22 : $i, X23 : $i]:
% 24.30/24.48         (((k3_subset_1 @ X22 @ X23) = (k6_subset_1 @ X22 @ X23))
% 24.30/24.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 24.30/24.48      inference('demod', [status(thm)], ['78', '79'])).
% 24.30/24.48  thf('81', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 24.30/24.48           = (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 24.30/24.48      inference('sup-', [status(thm)], ['77', '80'])).
% 24.30/24.48  thf('82', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.30/24.48         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 24.30/24.48          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ X1)
% 24.30/24.48              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 24.30/24.48                 (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))))),
% 24.30/24.48      inference('demod', [status(thm)], ['76', '81'])).
% 24.30/24.48  thf('83', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ X1)
% 24.30/24.48           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ 
% 24.30/24.48              (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['73', '82'])).
% 24.30/24.48  thf('84', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.30/24.48      inference('sup+', [status(thm)], ['69', '72'])).
% 24.30/24.48  thf('85', plain,
% 24.30/24.48      (![X39 : $i, X40 : $i, X41 : $i]:
% 24.30/24.48         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 24.30/24.48          | ((k7_subset_1 @ X40 @ X39 @ X41) = (k6_subset_1 @ X39 @ X41)))),
% 24.30/24.48      inference('demod', [status(thm)], ['21', '22'])).
% 24.30/24.48  thf('86', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.30/24.48         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ X2)
% 24.30/24.48           = (k6_subset_1 @ X0 @ X2))),
% 24.30/24.48      inference('sup-', [status(thm)], ['84', '85'])).
% 24.30/24.48  thf('87', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X0 @ X1)
% 24.30/24.48           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ 
% 24.30/24.48              (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['83', '86'])).
% 24.30/24.48  thf('88', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['70', '71'])).
% 24.30/24.48  thf(involutiveness_k3_subset_1, axiom,
% 24.30/24.48    (![A:$i,B:$i]:
% 24.30/24.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 24.30/24.48       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 24.30/24.48  thf('89', plain,
% 24.30/24.48      (![X32 : $i, X33 : $i]:
% 24.30/24.48         (((k3_subset_1 @ X33 @ (k3_subset_1 @ X33 @ X32)) = (X32))
% 24.30/24.48          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 24.30/24.48      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 24.30/24.48  thf('90', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 24.30/24.48           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 24.30/24.48      inference('sup-', [status(thm)], ['88', '89'])).
% 24.30/24.48  thf('91', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 24.30/24.48           = (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 24.30/24.48      inference('sup-', [status(thm)], ['77', '80'])).
% 24.30/24.48  thf('92', plain,
% 24.30/24.48      (![X26 : $i, X27 : $i]:
% 24.30/24.48         (m1_subset_1 @ (k6_subset_1 @ X26 @ X27) @ (k1_zfmisc_1 @ X26))),
% 24.30/24.48      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 24.30/24.48  thf('93', plain,
% 24.30/24.48      (![X22 : $i, X23 : $i]:
% 24.30/24.48         (((k3_subset_1 @ X22 @ X23) = (k6_subset_1 @ X22 @ X23))
% 24.30/24.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 24.30/24.48      inference('demod', [status(thm)], ['78', '79'])).
% 24.30/24.48  thf('94', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 24.30/24.48           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['92', '93'])).
% 24.30/24.48  thf('95', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 24.30/24.48           (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 24.30/24.48      inference('demod', [status(thm)], ['90', '91', '94'])).
% 24.30/24.48  thf('96', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 24.30/24.48      inference('sup-', [status(thm)], ['26', '27'])).
% 24.30/24.48  thf(t43_xboole_1, axiom,
% 24.30/24.48    (![A:$i,B:$i,C:$i]:
% 24.30/24.48     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 24.30/24.48       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 24.30/24.48  thf('97', plain,
% 24.30/24.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 24.30/24.48         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 24.30/24.48          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 24.30/24.48      inference('cnf', [status(esa)], [t43_xboole_1])).
% 24.30/24.48  thf('98', plain,
% 24.30/24.48      (![X37 : $i, X38 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 24.30/24.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 24.30/24.48  thf('99', plain,
% 24.30/24.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 24.30/24.48         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 24.30/24.48          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 24.30/24.48      inference('demod', [status(thm)], ['97', '98'])).
% 24.30/24.48  thf('100', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.30/24.48         (r1_tarski @ 
% 24.30/24.48          (k6_subset_1 @ (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1) @ 
% 24.30/24.48          X0)),
% 24.30/24.48      inference('sup-', [status(thm)], ['96', '99'])).
% 24.30/24.48  thf('101', plain,
% 24.30/24.48      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 24.30/24.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 24.30/24.48  thf('102', plain,
% 24.30/24.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 24.30/24.48         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 24.30/24.48          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 24.30/24.48      inference('demod', [status(thm)], ['97', '98'])).
% 24.30/24.48  thf('103', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 24.30/24.48      inference('sup-', [status(thm)], ['101', '102'])).
% 24.30/24.48  thf('104', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 24.30/24.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 24.30/24.48  thf(t1_boole, axiom,
% 24.30/24.48    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 24.30/24.48  thf('105', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 24.30/24.48      inference('cnf', [status(esa)], [t1_boole])).
% 24.30/24.48  thf('106', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['104', '105'])).
% 24.30/24.48  thf('107', plain,
% 24.30/24.48      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 24.30/24.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 24.30/24.48  thf('108', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 24.30/24.48      inference('sup+', [status(thm)], ['106', '107'])).
% 24.30/24.48  thf('109', plain,
% 24.30/24.48      (![X2 : $i, X4 : $i]:
% 24.30/24.48         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 24.30/24.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 24.30/24.48  thf('110', plain,
% 24.30/24.48      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['108', '109'])).
% 24.30/24.48  thf('111', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 24.30/24.48      inference('sup-', [status(thm)], ['103', '110'])).
% 24.30/24.48  thf('112', plain,
% 24.30/24.48      (![X16 : $i, X17 : $i]:
% 24.30/24.48         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 24.30/24.48           = (X16))),
% 24.30/24.48      inference('demod', [status(thm)], ['58', '59', '60'])).
% 24.30/24.48  thf('113', plain,
% 24.30/24.48      (![X0 : $i]:
% 24.30/24.48         ((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)) = (X0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['111', '112'])).
% 24.30/24.48  thf('114', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['104', '105'])).
% 24.30/24.48  thf('115', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 24.30/24.48      inference('demod', [status(thm)], ['113', '114'])).
% 24.30/24.48  thf(t100_xboole_1, axiom,
% 24.30/24.48    (![A:$i,B:$i]:
% 24.30/24.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 24.30/24.48  thf('116', plain,
% 24.30/24.48      (![X5 : $i, X6 : $i]:
% 24.30/24.48         ((k4_xboole_0 @ X5 @ X6)
% 24.30/24.48           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 24.30/24.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 24.30/24.48  thf('117', plain,
% 24.30/24.48      (![X37 : $i, X38 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))),
% 24.30/24.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 24.30/24.48  thf('118', plain,
% 24.30/24.48      (![X5 : $i, X6 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X5 @ X6)
% 24.30/24.48           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 24.30/24.48      inference('demod', [status(thm)], ['116', '117'])).
% 24.30/24.48  thf('119', plain,
% 24.30/24.48      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['115', '118'])).
% 24.30/24.48  thf('120', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 24.30/24.48      inference('sup-', [status(thm)], ['103', '110'])).
% 24.30/24.48  thf('121', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['119', '120'])).
% 24.30/24.48  thf('122', plain,
% 24.30/24.48      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['108', '109'])).
% 24.30/24.48  thf('123', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['121', '122'])).
% 24.30/24.48  thf('124', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.30/24.48         ((k6_subset_1 @ 
% 24.30/24.48           (k6_subset_1 @ (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ X2) @ 
% 24.30/24.48           X1) = (k1_xboole_0))),
% 24.30/24.48      inference('sup-', [status(thm)], ['100', '123'])).
% 24.30/24.48  thf('125', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['119', '120'])).
% 24.30/24.48  thf('126', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 24.30/24.48      inference('cnf', [status(esa)], [t1_boole])).
% 24.30/24.48  thf('127', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 24.30/24.48      inference('sup+', [status(thm)], ['125', '126'])).
% 24.30/24.48  thf('128', plain,
% 24.30/24.48      (![X1 : $i, X2 : $i]:
% 24.30/24.48         ((k6_subset_1 @ (k6_subset_1 @ X1 @ X2) @ X1) = (k1_xboole_0))),
% 24.30/24.48      inference('demod', [status(thm)], ['124', '127'])).
% 24.30/24.48  thf('129', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['95', '128'])).
% 24.30/24.48  thf('130', plain,
% 24.30/24.48      (![X16 : $i, X17 : $i]:
% 24.30/24.48         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 24.30/24.48           = (X16))),
% 24.30/24.48      inference('demod', [status(thm)], ['58', '59', '60'])).
% 24.30/24.48  thf('131', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k2_xboole_0 @ k1_xboole_0 @ 
% 24.30/24.48           (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))) = (X0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['129', '130'])).
% 24.30/24.48  thf('132', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['104', '105'])).
% 24.30/24.48  thf('133', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 24.30/24.48      inference('demod', [status(thm)], ['131', '132'])).
% 24.30/24.48  thf('134', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 24.30/24.48      inference('sup+', [status(thm)], ['65', '66'])).
% 24.30/24.48  thf('135', plain,
% 24.30/24.48      (![X5 : $i, X6 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X5 @ X6)
% 24.30/24.48           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 24.30/24.48      inference('demod', [status(thm)], ['116', '117'])).
% 24.30/24.48  thf('136', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X0 @ X1)
% 24.30/24.48           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 24.30/24.48      inference('sup+', [status(thm)], ['134', '135'])).
% 24.30/24.48  thf('137', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 24.30/24.48           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['133', '136'])).
% 24.30/24.48  thf('138', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X0 @ X1)
% 24.30/24.48           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ 
% 24.30/24.48              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['87', '137'])).
% 24.30/24.48  thf('139', plain,
% 24.30/24.48      ((((k6_subset_1 @ 
% 24.30/24.48          (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 24.30/24.48          (k2_tops_1 @ sk_A @ sk_B_1))
% 24.30/24.48          = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 24.30/24.48             (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 24.30/24.48             (k5_xboole_0 @ 
% 24.30/24.48              (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 24.30/24.48               (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))) @ 
% 24.30/24.48              (k2_tops_1 @ sk_A @ sk_B_1)))))
% 24.30/24.48         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 24.30/24.48      inference('sup+', [status(thm)], ['68', '138'])).
% 24.30/24.48  thf('140', plain,
% 24.30/24.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf('141', plain,
% 24.30/24.48      (![X32 : $i, X33 : $i]:
% 24.30/24.48         (((k3_subset_1 @ X33 @ (k3_subset_1 @ X33 @ X32)) = (X32))
% 24.30/24.48          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 24.30/24.48      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 24.30/24.48  thf('142', plain,
% 24.30/24.48      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 24.30/24.48      inference('sup-', [status(thm)], ['140', '141'])).
% 24.30/24.48  thf('143', plain,
% 24.30/24.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf('144', plain,
% 24.30/24.48      (![X22 : $i, X23 : $i]:
% 24.30/24.48         (((k3_subset_1 @ X22 @ X23) = (k6_subset_1 @ X22 @ X23))
% 24.30/24.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 24.30/24.48      inference('demod', [status(thm)], ['78', '79'])).
% 24.30/24.48  thf('145', plain,
% 24.30/24.48      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 24.30/24.48         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 24.30/24.48      inference('sup-', [status(thm)], ['143', '144'])).
% 24.30/24.48  thf('146', plain,
% 24.30/24.48      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 24.30/24.48      inference('demod', [status(thm)], ['142', '145'])).
% 24.30/24.48  thf('147', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 24.30/24.48           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['92', '93'])).
% 24.30/24.48  thf('148', plain,
% 24.30/24.48      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 24.30/24.48      inference('demod', [status(thm)], ['146', '147'])).
% 24.30/24.48  thf('149', plain,
% 24.30/24.48      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 24.30/24.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 24.30/24.48  thf('150', plain,
% 24.30/24.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf('151', plain,
% 24.30/24.48      (![X47 : $i, X48 : $i]:
% 24.30/24.48         ((r1_tarski @ X47 @ X48) | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48)))),
% 24.30/24.48      inference('cnf', [status(esa)], [t3_subset])).
% 24.30/24.48  thf('152', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 24.30/24.48      inference('sup-', [status(thm)], ['150', '151'])).
% 24.30/24.48  thf(t1_xboole_1, axiom,
% 24.30/24.48    (![A:$i,B:$i,C:$i]:
% 24.30/24.48     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 24.30/24.48       ( r1_tarski @ A @ C ) ))).
% 24.30/24.48  thf('153', plain,
% 24.30/24.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 24.30/24.48         (~ (r1_tarski @ X8 @ X9)
% 24.30/24.48          | ~ (r1_tarski @ X9 @ X10)
% 24.30/24.48          | (r1_tarski @ X8 @ X10))),
% 24.30/24.48      inference('cnf', [status(esa)], [t1_xboole_1])).
% 24.30/24.48  thf('154', plain,
% 24.30/24.48      (![X0 : $i]:
% 24.30/24.48         ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 24.30/24.48      inference('sup-', [status(thm)], ['152', '153'])).
% 24.30/24.48  thf('155', plain,
% 24.30/24.48      (![X0 : $i]:
% 24.30/24.48         (r1_tarski @ sk_B_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 24.30/24.48      inference('sup-', [status(thm)], ['149', '154'])).
% 24.30/24.48  thf('156', plain,
% 24.30/24.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 24.30/24.48         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 24.30/24.48          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 24.30/24.48      inference('demod', [status(thm)], ['97', '98'])).
% 24.30/24.48  thf('157', plain,
% 24.30/24.48      (![X0 : $i]:
% 24.30/24.48         (r1_tarski @ (k6_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0)),
% 24.30/24.48      inference('sup-', [status(thm)], ['155', '156'])).
% 24.30/24.48  thf('158', plain,
% 24.30/24.48      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['108', '109'])).
% 24.30/24.48  thf('159', plain,
% 24.30/24.48      (((k6_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 24.30/24.48      inference('sup-', [status(thm)], ['157', '158'])).
% 24.30/24.48  thf('160', plain,
% 24.30/24.48      (![X16 : $i, X17 : $i]:
% 24.30/24.48         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 24.30/24.48           = (X16))),
% 24.30/24.48      inference('demod', [status(thm)], ['58', '59', '60'])).
% 24.30/24.48  thf('161', plain,
% 24.30/24.48      (((k2_xboole_0 @ k1_xboole_0 @ 
% 24.30/24.48         (k3_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A))) = (sk_B_1))),
% 24.30/24.48      inference('sup+', [status(thm)], ['159', '160'])).
% 24.30/24.48  thf('162', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['104', '105'])).
% 24.30/24.48  thf('163', plain,
% 24.30/24.48      (((k3_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (sk_B_1))),
% 24.30/24.48      inference('demod', [status(thm)], ['161', '162'])).
% 24.30/24.48  thf('164', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X0 @ X1)
% 24.30/24.48           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 24.30/24.48      inference('sup+', [status(thm)], ['134', '135'])).
% 24.30/24.48  thf('165', plain,
% 24.30/24.48      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 24.30/24.48         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 24.30/24.48      inference('sup+', [status(thm)], ['163', '164'])).
% 24.30/24.48  thf('166', plain,
% 24.30/24.48      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 24.30/24.48      inference('demod', [status(thm)], ['148', '165'])).
% 24.30/24.48  thf('167', plain,
% 24.30/24.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf(dt_k2_tops_1, axiom,
% 24.30/24.48    (![A:$i,B:$i]:
% 24.30/24.48     ( ( ( l1_pre_topc @ A ) & 
% 24.30/24.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 24.30/24.48       ( m1_subset_1 @
% 24.30/24.48         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 24.30/24.48  thf('168', plain,
% 24.30/24.48      (![X52 : $i, X53 : $i]:
% 24.30/24.48         (~ (l1_pre_topc @ X52)
% 24.30/24.48          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 24.30/24.48          | (m1_subset_1 @ (k2_tops_1 @ X52 @ X53) @ 
% 24.30/24.48             (k1_zfmisc_1 @ (u1_struct_0 @ X52))))),
% 24.30/24.48      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 24.30/24.48  thf('169', plain,
% 24.30/24.48      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 24.30/24.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 24.30/24.48        | ~ (l1_pre_topc @ sk_A))),
% 24.30/24.48      inference('sup-', [status(thm)], ['167', '168'])).
% 24.30/24.48  thf('170', plain, ((l1_pre_topc @ sk_A)),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf('171', plain,
% 24.30/24.48      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 24.30/24.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.30/24.48      inference('demod', [status(thm)], ['169', '170'])).
% 24.30/24.48  thf('172', plain,
% 24.30/24.48      (![X26 : $i, X27 : $i]:
% 24.30/24.48         (m1_subset_1 @ (k6_subset_1 @ X26 @ X27) @ (k1_zfmisc_1 @ X26))),
% 24.30/24.48      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 24.30/24.48  thf(redefinition_k4_subset_1, axiom,
% 24.30/24.48    (![A:$i,B:$i,C:$i]:
% 24.30/24.48     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 24.30/24.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 24.30/24.48       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 24.30/24.48  thf('173', plain,
% 24.30/24.48      (![X34 : $i, X35 : $i, X36 : $i]:
% 24.30/24.48         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 24.30/24.48          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 24.30/24.48          | ((k4_subset_1 @ X35 @ X34 @ X36) = (k2_xboole_0 @ X34 @ X36)))),
% 24.30/24.48      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 24.30/24.48  thf('174', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.30/24.48         (((k4_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X2)
% 24.30/24.48            = (k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X2))
% 24.30/24.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['172', '173'])).
% 24.30/24.48  thf('175', plain,
% 24.30/24.48      (![X0 : $i]:
% 24.30/24.48         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 24.30/24.48           (k2_tops_1 @ sk_A @ sk_B_1))
% 24.30/24.48           = (k2_xboole_0 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 24.30/24.48              (k2_tops_1 @ sk_A @ sk_B_1)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['171', '174'])).
% 24.30/24.48  thf('176', plain,
% 24.30/24.48      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 24.30/24.48         (k2_tops_1 @ sk_A @ sk_B_1))
% 24.30/24.48         = (k2_xboole_0 @ 
% 24.30/24.48            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 24.30/24.48            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 24.30/24.48      inference('sup+', [status(thm)], ['166', '175'])).
% 24.30/24.48  thf('177', plain,
% 24.30/24.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf(t65_tops_1, axiom,
% 24.30/24.48    (![A:$i]:
% 24.30/24.48     ( ( l1_pre_topc @ A ) =>
% 24.30/24.48       ( ![B:$i]:
% 24.30/24.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.30/24.48           ( ( k2_pre_topc @ A @ B ) =
% 24.30/24.48             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 24.30/24.48  thf('178', plain,
% 24.30/24.48      (![X63 : $i, X64 : $i]:
% 24.30/24.48         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 24.30/24.48          | ((k2_pre_topc @ X64 @ X63)
% 24.30/24.48              = (k4_subset_1 @ (u1_struct_0 @ X64) @ X63 @ 
% 24.30/24.48                 (k2_tops_1 @ X64 @ X63)))
% 24.30/24.48          | ~ (l1_pre_topc @ X64))),
% 24.30/24.48      inference('cnf', [status(esa)], [t65_tops_1])).
% 24.30/24.48  thf('179', plain,
% 24.30/24.48      ((~ (l1_pre_topc @ sk_A)
% 24.30/24.48        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 24.30/24.48            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 24.30/24.48               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 24.30/24.48      inference('sup-', [status(thm)], ['177', '178'])).
% 24.30/24.48  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf('181', plain,
% 24.30/24.48      (((k2_pre_topc @ sk_A @ sk_B_1)
% 24.30/24.48         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 24.30/24.48            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['179', '180'])).
% 24.30/24.48  thf('182', plain,
% 24.30/24.48      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 24.30/24.48      inference('demod', [status(thm)], ['148', '165'])).
% 24.30/24.48  thf('183', plain,
% 24.30/24.48      (((k2_pre_topc @ sk_A @ sk_B_1)
% 24.30/24.48         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['176', '181', '182'])).
% 24.30/24.48  thf('184', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 24.30/24.48      inference('demod', [status(thm)], ['131', '132'])).
% 24.30/24.48  thf('185', plain,
% 24.30/24.48      (((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 24.30/24.48      inference('sup+', [status(thm)], ['183', '184'])).
% 24.30/24.48  thf('186', plain,
% 24.30/24.48      (((k1_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['19', '24'])).
% 24.30/24.48  thf('187', plain,
% 24.30/24.48      (((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 24.30/24.48      inference('sup+', [status(thm)], ['183', '184'])).
% 24.30/24.48  thf('188', plain,
% 24.30/24.48      (((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 24.30/24.48      inference('sup+', [status(thm)], ['183', '184'])).
% 24.30/24.48  thf('189', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 24.30/24.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 24.30/24.48  thf('190', plain,
% 24.30/24.48      (((k2_pre_topc @ sk_A @ sk_B_1)
% 24.30/24.48         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['176', '181', '182'])).
% 24.30/24.48  thf('191', plain,
% 24.30/24.48      (((k2_pre_topc @ sk_A @ sk_B_1)
% 24.30/24.48         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['176', '181', '182'])).
% 24.30/24.48  thf('192', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 24.30/24.48           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['133', '136'])).
% 24.30/24.48  thf('193', plain,
% 24.30/24.48      (((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 24.30/24.48         = (k5_xboole_0 @ 
% 24.30/24.48            (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) @ sk_B_1))),
% 24.30/24.48      inference('sup+', [status(thm)], ['191', '192'])).
% 24.30/24.48  thf('194', plain,
% 24.30/24.48      (((k2_pre_topc @ sk_A @ sk_B_1)
% 24.30/24.48         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['176', '181', '182'])).
% 24.30/24.48  thf('195', plain,
% 24.30/24.48      (((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 24.30/24.48         = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 24.30/24.48      inference('demod', [status(thm)], ['193', '194'])).
% 24.30/24.48  thf('196', plain,
% 24.30/24.48      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 24.30/24.48         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 24.30/24.48      inference('sup+', [status(thm)], ['55', '56'])).
% 24.30/24.48  thf('197', plain,
% 24.30/24.48      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48          = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 24.30/24.48         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 24.30/24.48      inference('sup+', [status(thm)], ['195', '196'])).
% 24.30/24.48  thf('198', plain,
% 24.30/24.48      (((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 24.30/24.48         = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 24.30/24.48      inference('demod', [status(thm)], ['193', '194'])).
% 24.30/24.48  thf('199', plain,
% 24.30/24.48      (![X16 : $i, X17 : $i]:
% 24.30/24.48         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 24.30/24.48           = (X16))),
% 24.30/24.48      inference('demod', [status(thm)], ['58', '59', '60'])).
% 24.30/24.48  thf('200', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 24.30/24.48           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['133', '136'])).
% 24.30/24.48  thf('201', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 24.30/24.48           = (k5_xboole_0 @ 
% 24.30/24.48              (k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)) @ 
% 24.30/24.48              (k6_subset_1 @ X0 @ X1)))),
% 24.30/24.48      inference('sup+', [status(thm)], ['199', '200'])).
% 24.30/24.48  thf('202', plain,
% 24.30/24.48      (![X16 : $i, X17 : $i]:
% 24.30/24.48         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 24.30/24.48           = (X16))),
% 24.30/24.48      inference('demod', [status(thm)], ['58', '59', '60'])).
% 24.30/24.48  thf('203', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.30/24.48      inference('sup+', [status(thm)], ['69', '72'])).
% 24.30/24.48  thf('204', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['202', '203'])).
% 24.30/24.48  thf('205', plain,
% 24.30/24.48      (![X32 : $i, X33 : $i]:
% 24.30/24.48         (((k3_subset_1 @ X33 @ (k3_subset_1 @ X33 @ X32)) = (X32))
% 24.30/24.48          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 24.30/24.48      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 24.30/24.48  thf('206', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 24.30/24.48           = (k3_xboole_0 @ X0 @ X1))),
% 24.30/24.48      inference('sup-', [status(thm)], ['204', '205'])).
% 24.30/24.48  thf('207', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['202', '203'])).
% 24.30/24.48  thf('208', plain,
% 24.30/24.48      (![X22 : $i, X23 : $i]:
% 24.30/24.48         (((k3_subset_1 @ X22 @ X23) = (k6_subset_1 @ X22 @ X23))
% 24.30/24.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 24.30/24.48      inference('demod', [status(thm)], ['78', '79'])).
% 24.30/24.48  thf('209', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 24.30/24.48           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['207', '208'])).
% 24.30/24.48  thf('210', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 24.30/24.48           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 24.30/24.48      inference('sup-', [status(thm)], ['92', '93'])).
% 24.30/24.48  thf('211', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 24.30/24.48           = (k3_xboole_0 @ X0 @ X1))),
% 24.30/24.48      inference('demod', [status(thm)], ['206', '209', '210'])).
% 24.30/24.48  thf('212', plain,
% 24.30/24.48      (![X16 : $i, X17 : $i]:
% 24.30/24.48         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 24.30/24.48           = (X16))),
% 24.30/24.48      inference('demod', [status(thm)], ['58', '59', '60'])).
% 24.30/24.48  thf('213', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 24.30/24.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 24.30/24.48  thf('214', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['95', '128'])).
% 24.30/24.48  thf('215', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['213', '214'])).
% 24.30/24.48  thf('216', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['212', '215'])).
% 24.30/24.48  thf('217', plain,
% 24.30/24.48      (![X16 : $i, X17 : $i]:
% 24.30/24.48         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 24.30/24.48           = (X16))),
% 24.30/24.48      inference('demod', [status(thm)], ['58', '59', '60'])).
% 24.30/24.48  thf('218', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k2_xboole_0 @ k1_xboole_0 @ 
% 24.30/24.48           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))
% 24.30/24.48           = (k3_xboole_0 @ X1 @ X0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['216', '217'])).
% 24.30/24.48  thf('219', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 24.30/24.48      inference('sup+', [status(thm)], ['65', '66'])).
% 24.30/24.48  thf('220', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 24.30/24.48      inference('sup+', [status(thm)], ['104', '105'])).
% 24.30/24.48  thf('221', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 24.30/24.48           = (k3_xboole_0 @ X1 @ X0))),
% 24.30/24.48      inference('demod', [status(thm)], ['218', '219', '220'])).
% 24.30/24.48  thf('222', plain,
% 24.30/24.48      (![X5 : $i, X6 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X5 @ X6)
% 24.30/24.48           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 24.30/24.48      inference('demod', [status(thm)], ['116', '117'])).
% 24.30/24.48  thf('223', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 24.30/24.48           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 24.30/24.48      inference('sup+', [status(thm)], ['221', '222'])).
% 24.30/24.48  thf('224', plain,
% 24.30/24.48      (![X5 : $i, X6 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X5 @ X6)
% 24.30/24.48           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 24.30/24.48      inference('demod', [status(thm)], ['116', '117'])).
% 24.30/24.48  thf('225', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 24.30/24.48           = (k6_subset_1 @ X1 @ X0))),
% 24.30/24.48      inference('demod', [status(thm)], ['223', '224'])).
% 24.30/24.48  thf('226', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 24.30/24.48           = (k3_xboole_0 @ X0 @ X1))),
% 24.30/24.48      inference('demod', [status(thm)], ['211', '225'])).
% 24.30/24.48  thf('227', plain,
% 24.30/24.48      (![X16 : $i, X17 : $i]:
% 24.30/24.48         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 24.30/24.48           = (X16))),
% 24.30/24.48      inference('demod', [status(thm)], ['58', '59', '60'])).
% 24.30/24.48  thf('228', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]:
% 24.30/24.48         ((k3_xboole_0 @ X0 @ X1)
% 24.30/24.48           = (k5_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['201', '226', '227'])).
% 24.30/24.48  thf('229', plain,
% 24.30/24.48      (((k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 24.30/24.48         = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 24.30/24.48            (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))),
% 24.30/24.48      inference('sup+', [status(thm)], ['198', '228'])).
% 24.30/24.48  thf('230', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 24.30/24.48      inference('sup+', [status(thm)], ['65', '66'])).
% 24.30/24.48  thf('231', plain,
% 24.30/24.48      (((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 24.30/24.48      inference('sup+', [status(thm)], ['183', '184'])).
% 24.30/24.48  thf('232', plain,
% 24.30/24.48      (((sk_B_1)
% 24.30/24.48         = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 24.30/24.48            (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))),
% 24.30/24.48      inference('demod', [status(thm)], ['229', '230', '231'])).
% 24.30/24.48  thf('233', plain,
% 24.30/24.48      ((((sk_B_1)
% 24.30/24.48          = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 24.30/24.48             (k2_tops_1 @ sk_A @ sk_B_1))))
% 24.30/24.48         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 24.30/24.48      inference('sup+', [status(thm)], ['197', '232'])).
% 24.30/24.48  thf('234', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 24.30/24.48      inference('simplify', [status(thm)], ['12'])).
% 24.30/24.48  thf('235', plain,
% 24.30/24.48      (![X47 : $i, X49 : $i]:
% 24.30/24.48         ((m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X49)) | ~ (r1_tarski @ X47 @ X49))),
% 24.30/24.48      inference('cnf', [status(esa)], [t3_subset])).
% 24.30/24.48  thf('236', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 24.30/24.48      inference('sup-', [status(thm)], ['234', '235'])).
% 24.30/24.48  thf(idempotence_k9_subset_1, axiom,
% 24.30/24.48    (![A:$i,B:$i,C:$i]:
% 24.30/24.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 24.30/24.48       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 24.30/24.48  thf('237', plain,
% 24.30/24.48      (![X29 : $i, X30 : $i, X31 : $i]:
% 24.30/24.48         (((k9_subset_1 @ X30 @ X29 @ X29) = (X29))
% 24.30/24.48          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 24.30/24.48      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 24.30/24.48  thf('238', plain,
% 24.30/24.48      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 24.30/24.48      inference('sup-', [status(thm)], ['236', '237'])).
% 24.30/24.48  thf('239', plain,
% 24.30/24.48      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 24.30/24.48         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 24.30/24.48      inference('demod', [status(thm)],
% 24.30/24.48                ['139', '185', '186', '187', '188', '189', '190', '233', '238'])).
% 24.30/24.48  thf('240', plain,
% 24.30/24.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf(fc9_tops_1, axiom,
% 24.30/24.48    (![A:$i,B:$i]:
% 24.30/24.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 24.30/24.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 24.30/24.48       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 24.30/24.48  thf('241', plain,
% 24.30/24.48      (![X54 : $i, X55 : $i]:
% 24.30/24.48         (~ (l1_pre_topc @ X54)
% 24.30/24.48          | ~ (v2_pre_topc @ X54)
% 24.30/24.48          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 24.30/24.48          | (v3_pre_topc @ (k1_tops_1 @ X54 @ X55) @ X54))),
% 24.30/24.48      inference('cnf', [status(esa)], [fc9_tops_1])).
% 24.30/24.48  thf('242', plain,
% 24.30/24.48      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 24.30/24.48        | ~ (v2_pre_topc @ sk_A)
% 24.30/24.48        | ~ (l1_pre_topc @ sk_A))),
% 24.30/24.48      inference('sup-', [status(thm)], ['240', '241'])).
% 24.30/24.48  thf('243', plain, ((v2_pre_topc @ sk_A)),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf('244', plain, ((l1_pre_topc @ sk_A)),
% 24.30/24.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.30/24.48  thf('245', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 24.30/24.48      inference('demod', [status(thm)], ['242', '243', '244'])).
% 24.30/24.48  thf('246', plain,
% 24.30/24.48      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 24.30/24.48         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 24.30/24.48      inference('sup+', [status(thm)], ['239', '245'])).
% 24.30/24.48  thf('247', plain,
% 24.30/24.48      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 24.30/24.48      inference('split', [status(esa)], ['0'])).
% 24.30/24.48  thf('248', plain,
% 24.30/24.48      (~
% 24.30/24.48       (((k2_tops_1 @ sk_A @ sk_B_1)
% 24.30/24.48          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.30/24.48             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 24.30/24.48       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 24.30/24.48      inference('sup-', [status(thm)], ['246', '247'])).
% 24.30/24.48  thf('249', plain, ($false),
% 24.30/24.48      inference('sat_resolution*', [status(thm)], ['1', '53', '54', '248'])).
% 24.30/24.48  
% 24.30/24.48  % SZS output end Refutation
% 24.30/24.48  
% 24.30/24.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
