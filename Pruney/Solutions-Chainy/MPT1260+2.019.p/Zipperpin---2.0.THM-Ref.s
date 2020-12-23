%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XxlbedFJEK

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:25 EST 2020

% Result     : Theorem 2.43s
% Output     : Refutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 360 expanded)
%              Number of leaves         :   45 ( 125 expanded)
%              Depth                    :   17
%              Number of atoms          : 1520 (3793 expanded)
%              Number of equality atoms :  112 ( 266 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ~ ( v3_pre_topc @ X59 @ X60 )
      | ~ ( r1_tarski @ X59 @ X61 )
      | ( r1_tarski @ X59 @ ( k1_tops_1 @ X60 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
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
    ! [X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ( ( k1_tops_1 @ X65 @ X64 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X65 ) @ X64 @ ( k2_tops_1 @ X65 @ X64 ) ) )
      | ~ ( l1_pre_topc @ X65 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X40 @ X42 )
        = ( k4_xboole_0 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X40 @ X42 )
        = ( k6_subset_1 @ X40 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k6_subset_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X27: $i,X28: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','30'])).

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
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( ( k2_tops_1 @ X58 @ X57 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X58 ) @ ( k2_pre_topc @ X58 @ X57 ) @ ( k1_tops_1 @ X58 @ X57 ) ) )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( l1_pre_topc @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X51 @ X52 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X40 @ X42 )
        = ( k6_subset_1 @ X40 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['34','35','42'])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['31','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('51',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('52',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('53',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k6_subset_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('54',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('55',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('56',plain,(
    ! [X16: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('58',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('60',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k6_subset_1 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k6_subset_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','62'])).

thf('64',plain,(
    ! [X16: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('66',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X22 @ X21 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('67',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('71',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('72',plain,(
    ! [X48: $i,X50: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X50 ) )
      | ~ ( r1_tarski @ X48 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('74',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ( r2_hidden @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k6_subset_1 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ X1 )
          = k1_xboole_0 )
        | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ X1 ) @ X0 @ k1_xboole_0 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,
    ( ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['77','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('90',plain,
    ( ( ( ( k3_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
        = k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('92',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('93',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('94',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k6_subset_1 @ X17 @ X18 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['91','94'])).

thf('96',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('98',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('99',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','100'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('102',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('103',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('104',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X16: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('107',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('108',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k6_subset_1 @ X38 @ X39 )
      = ( k4_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('109',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k6_subset_1 @ X20 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['106','109'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('111',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['105','112'])).

thf('114',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k6_subset_1 @ X17 @ X18 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','100'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['95','96','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('120',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( l1_pre_topc @ X55 )
      | ~ ( v2_pre_topc @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X55 @ X56 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('121',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['118','124'])).

thf('126',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('127',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','49','50','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XxlbedFJEK
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:25:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.43/2.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.43/2.62  % Solved by: fo/fo7.sh
% 2.43/2.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.43/2.62  % done 3575 iterations in 2.167s
% 2.43/2.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.43/2.62  % SZS output start Refutation
% 2.43/2.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.43/2.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.43/2.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.43/2.62  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.43/2.62  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.43/2.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.43/2.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.43/2.62  thf(sk_A_type, type, sk_A: $i).
% 2.43/2.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.43/2.62  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 2.43/2.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.43/2.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.43/2.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.43/2.62  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 2.43/2.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.43/2.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.43/2.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.43/2.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.43/2.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.43/2.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.43/2.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.43/2.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.43/2.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.43/2.62  thf(t76_tops_1, conjecture,
% 2.43/2.62    (![A:$i]:
% 2.43/2.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.43/2.62       ( ![B:$i]:
% 2.43/2.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.43/2.62           ( ( v3_pre_topc @ B @ A ) <=>
% 2.43/2.62             ( ( k2_tops_1 @ A @ B ) =
% 2.43/2.62               ( k7_subset_1 @
% 2.43/2.62                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 2.43/2.62  thf(zf_stmt_0, negated_conjecture,
% 2.43/2.62    (~( ![A:$i]:
% 2.43/2.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.43/2.62          ( ![B:$i]:
% 2.43/2.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.43/2.62              ( ( v3_pre_topc @ B @ A ) <=>
% 2.43/2.62                ( ( k2_tops_1 @ A @ B ) =
% 2.43/2.62                  ( k7_subset_1 @
% 2.43/2.62                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 2.43/2.62    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 2.43/2.62  thf('0', plain,
% 2.43/2.62      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.62              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 2.43/2.62        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.43/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.62  thf('1', plain,
% 2.43/2.62      (~
% 2.43/2.62       (((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.62             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 2.43/2.62       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.43/2.62      inference('split', [status(esa)], ['0'])).
% 2.43/2.62  thf('2', plain,
% 2.43/2.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.43/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.62  thf('3', plain,
% 2.43/2.62      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.62             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 2.43/2.62        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.43/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.62  thf('4', plain,
% 2.43/2.62      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.43/2.62      inference('split', [status(esa)], ['3'])).
% 2.43/2.62  thf('5', plain,
% 2.43/2.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.43/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.62  thf(t56_tops_1, axiom,
% 2.43/2.62    (![A:$i]:
% 2.43/2.62     ( ( l1_pre_topc @ A ) =>
% 2.43/2.62       ( ![B:$i]:
% 2.43/2.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.43/2.62           ( ![C:$i]:
% 2.43/2.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.43/2.62               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 2.43/2.62                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.43/2.62  thf('6', plain,
% 2.43/2.62      (![X59 : $i, X60 : $i, X61 : $i]:
% 2.43/2.62         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 2.43/2.62          | ~ (v3_pre_topc @ X59 @ X60)
% 2.43/2.62          | ~ (r1_tarski @ X59 @ X61)
% 2.43/2.62          | (r1_tarski @ X59 @ (k1_tops_1 @ X60 @ X61))
% 2.43/2.62          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 2.43/2.62          | ~ (l1_pre_topc @ X60))),
% 2.43/2.62      inference('cnf', [status(esa)], [t56_tops_1])).
% 2.43/2.62  thf('7', plain,
% 2.43/2.62      (![X0 : $i]:
% 2.43/2.62         (~ (l1_pre_topc @ sk_A)
% 2.43/2.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.43/2.62          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 2.43/2.62          | ~ (r1_tarski @ sk_B_1 @ X0)
% 2.43/2.62          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.43/2.62      inference('sup-', [status(thm)], ['5', '6'])).
% 2.43/2.62  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 2.43/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.62  thf('9', plain,
% 2.43/2.62      (![X0 : $i]:
% 2.43/2.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.43/2.62          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 2.43/2.62          | ~ (r1_tarski @ sk_B_1 @ X0)
% 2.43/2.62          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.43/2.62      inference('demod', [status(thm)], ['7', '8'])).
% 2.43/2.62  thf('10', plain,
% 2.43/2.62      ((![X0 : $i]:
% 2.43/2.62          (~ (r1_tarski @ sk_B_1 @ X0)
% 2.43/2.62           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 2.43/2.62           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 2.43/2.62         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.43/2.62      inference('sup-', [status(thm)], ['4', '9'])).
% 2.43/2.62  thf('11', plain,
% 2.43/2.62      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 2.43/2.62         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 2.43/2.62         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.43/2.62      inference('sup-', [status(thm)], ['2', '10'])).
% 2.43/2.62  thf(d10_xboole_0, axiom,
% 2.43/2.62    (![A:$i,B:$i]:
% 2.43/2.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.43/2.62  thf('12', plain,
% 2.43/2.62      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 2.43/2.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.43/2.62  thf('13', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 2.43/2.62      inference('simplify', [status(thm)], ['12'])).
% 2.43/2.62  thf('14', plain,
% 2.43/2.62      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 2.43/2.62         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.43/2.62      inference('demod', [status(thm)], ['11', '13'])).
% 2.43/2.62  thf('15', plain,
% 2.43/2.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.43/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.62  thf(t74_tops_1, axiom,
% 2.43/2.62    (![A:$i]:
% 2.43/2.62     ( ( l1_pre_topc @ A ) =>
% 2.43/2.62       ( ![B:$i]:
% 2.43/2.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.43/2.62           ( ( k1_tops_1 @ A @ B ) =
% 2.43/2.62             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.43/2.62  thf('16', plain,
% 2.43/2.62      (![X64 : $i, X65 : $i]:
% 2.43/2.62         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 2.43/2.62          | ((k1_tops_1 @ X65 @ X64)
% 2.43/2.62              = (k7_subset_1 @ (u1_struct_0 @ X65) @ X64 @ 
% 2.43/2.62                 (k2_tops_1 @ X65 @ X64)))
% 2.43/2.62          | ~ (l1_pre_topc @ X65))),
% 2.43/2.62      inference('cnf', [status(esa)], [t74_tops_1])).
% 2.43/2.62  thf('17', plain,
% 2.43/2.62      ((~ (l1_pre_topc @ sk_A)
% 2.43/2.62        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 2.43/2.62               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 2.43/2.62      inference('sup-', [status(thm)], ['15', '16'])).
% 2.43/2.62  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 2.43/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.62  thf('19', plain,
% 2.43/2.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.43/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.62  thf(redefinition_k7_subset_1, axiom,
% 2.43/2.62    (![A:$i,B:$i,C:$i]:
% 2.43/2.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.43/2.62       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.43/2.62  thf('20', plain,
% 2.43/2.62      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.43/2.62         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 2.43/2.62          | ((k7_subset_1 @ X41 @ X40 @ X42) = (k4_xboole_0 @ X40 @ X42)))),
% 2.43/2.62      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.43/2.62  thf(redefinition_k6_subset_1, axiom,
% 2.43/2.62    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.43/2.62  thf('21', plain,
% 2.43/2.62      (![X38 : $i, X39 : $i]:
% 2.43/2.62         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 2.43/2.62      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.43/2.62  thf('22', plain,
% 2.43/2.62      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.43/2.62         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 2.43/2.62          | ((k7_subset_1 @ X41 @ X40 @ X42) = (k6_subset_1 @ X40 @ X42)))),
% 2.43/2.62      inference('demod', [status(thm)], ['20', '21'])).
% 2.43/2.62  thf('23', plain,
% 2.43/2.62      (![X0 : $i]:
% 2.43/2.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 2.43/2.62           = (k6_subset_1 @ sk_B_1 @ X0))),
% 2.43/2.62      inference('sup-', [status(thm)], ['19', '22'])).
% 2.43/2.62  thf('24', plain,
% 2.43/2.62      (((k1_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 2.43/2.62      inference('demod', [status(thm)], ['17', '18', '23'])).
% 2.43/2.62  thf(dt_k6_subset_1, axiom,
% 2.43/2.62    (![A:$i,B:$i]:
% 2.43/2.62     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.43/2.62  thf('25', plain,
% 2.43/2.62      (![X27 : $i, X28 : $i]:
% 2.43/2.62         (m1_subset_1 @ (k6_subset_1 @ X27 @ X28) @ (k1_zfmisc_1 @ X27))),
% 2.43/2.62      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 2.43/2.62  thf(t3_subset, axiom,
% 2.43/2.62    (![A:$i,B:$i]:
% 2.43/2.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.43/2.62  thf('26', plain,
% 2.43/2.62      (![X48 : $i, X49 : $i]:
% 2.43/2.62         ((r1_tarski @ X48 @ X49) | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49)))),
% 2.43/2.62      inference('cnf', [status(esa)], [t3_subset])).
% 2.43/2.62  thf('27', plain,
% 2.43/2.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 2.43/2.62      inference('sup-', [status(thm)], ['25', '26'])).
% 2.43/2.62  thf('28', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 2.43/2.62      inference('sup+', [status(thm)], ['24', '27'])).
% 2.43/2.62  thf('29', plain,
% 2.43/2.62      (![X7 : $i, X9 : $i]:
% 2.43/2.62         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 2.43/2.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.43/2.62  thf('30', plain,
% 2.43/2.62      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 2.43/2.62        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 2.43/2.62      inference('sup-', [status(thm)], ['28', '29'])).
% 2.43/2.62  thf('31', plain,
% 2.43/2.62      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 2.43/2.62         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.43/2.62      inference('sup-', [status(thm)], ['14', '30'])).
% 2.43/2.62  thf('32', plain,
% 2.43/2.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.43/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.62  thf(l78_tops_1, axiom,
% 2.43/2.62    (![A:$i]:
% 2.43/2.62     ( ( l1_pre_topc @ A ) =>
% 2.43/2.62       ( ![B:$i]:
% 2.43/2.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.43/2.62           ( ( k2_tops_1 @ A @ B ) =
% 2.43/2.62             ( k7_subset_1 @
% 2.43/2.62               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 2.43/2.62               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.43/2.62  thf('33', plain,
% 2.43/2.62      (![X57 : $i, X58 : $i]:
% 2.43/2.62         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 2.43/2.62          | ((k2_tops_1 @ X58 @ X57)
% 2.43/2.62              = (k7_subset_1 @ (u1_struct_0 @ X58) @ 
% 2.43/2.62                 (k2_pre_topc @ X58 @ X57) @ (k1_tops_1 @ X58 @ X57)))
% 2.43/2.62          | ~ (l1_pre_topc @ X58))),
% 2.43/2.62      inference('cnf', [status(esa)], [l78_tops_1])).
% 2.43/2.62  thf('34', plain,
% 2.43/2.62      ((~ (l1_pre_topc @ sk_A)
% 2.43/2.62        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.62               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 2.43/2.62      inference('sup-', [status(thm)], ['32', '33'])).
% 2.43/2.62  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 2.43/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.62  thf('36', plain,
% 2.43/2.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.43/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.62  thf(dt_k2_pre_topc, axiom,
% 2.43/2.62    (![A:$i,B:$i]:
% 2.43/2.62     ( ( ( l1_pre_topc @ A ) & 
% 2.43/2.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.43/2.62       ( m1_subset_1 @
% 2.43/2.62         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.43/2.62  thf('37', plain,
% 2.43/2.62      (![X51 : $i, X52 : $i]:
% 2.43/2.62         (~ (l1_pre_topc @ X51)
% 2.43/2.62          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 2.43/2.62          | (m1_subset_1 @ (k2_pre_topc @ X51 @ X52) @ 
% 2.43/2.62             (k1_zfmisc_1 @ (u1_struct_0 @ X51))))),
% 2.43/2.62      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.43/2.62  thf('38', plain,
% 2.43/2.62      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.43/2.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.43/2.62        | ~ (l1_pre_topc @ sk_A))),
% 2.43/2.62      inference('sup-', [status(thm)], ['36', '37'])).
% 2.43/2.62  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 2.43/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.62  thf('40', plain,
% 2.43/2.62      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.43/2.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.43/2.62      inference('demod', [status(thm)], ['38', '39'])).
% 2.43/2.62  thf('41', plain,
% 2.43/2.62      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.43/2.62         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 2.43/2.62          | ((k7_subset_1 @ X41 @ X40 @ X42) = (k6_subset_1 @ X40 @ X42)))),
% 2.43/2.62      inference('demod', [status(thm)], ['20', '21'])).
% 2.43/2.62  thf('42', plain,
% 2.43/2.62      (![X0 : $i]:
% 2.43/2.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.62           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 2.43/2.62           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 2.43/2.62      inference('sup-', [status(thm)], ['40', '41'])).
% 2.43/2.62  thf('43', plain,
% 2.43/2.62      (((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.43/2.62            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 2.43/2.62      inference('demod', [status(thm)], ['34', '35', '42'])).
% 2.43/2.62  thf('44', plain,
% 2.43/2.62      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 2.43/2.62         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.43/2.62      inference('sup+', [status(thm)], ['31', '43'])).
% 2.43/2.62  thf('45', plain,
% 2.43/2.62      (![X0 : $i]:
% 2.43/2.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.62           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 2.43/2.62           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 2.43/2.62      inference('sup-', [status(thm)], ['40', '41'])).
% 2.43/2.62  thf('46', plain,
% 2.43/2.62      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.62              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 2.43/2.62         <= (~
% 2.43/2.62             (((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.62                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.43/2.62      inference('split', [status(esa)], ['0'])).
% 2.43/2.62  thf('47', plain,
% 2.43/2.62      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62          != (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 2.43/2.62         <= (~
% 2.43/2.62             (((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.62                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.43/2.62      inference('sup-', [status(thm)], ['45', '46'])).
% 2.43/2.62  thf('48', plain,
% 2.43/2.62      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 2.43/2.62         <= (~
% 2.43/2.62             (((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.62                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 2.43/2.62             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.43/2.62      inference('sup-', [status(thm)], ['44', '47'])).
% 2.43/2.62  thf('49', plain,
% 2.43/2.62      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.62             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 2.43/2.62       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.43/2.62      inference('simplify', [status(thm)], ['48'])).
% 2.43/2.62  thf('50', plain,
% 2.43/2.62      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.62             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 2.43/2.62       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.43/2.62      inference('split', [status(esa)], ['3'])).
% 2.43/2.62  thf(d5_xboole_0, axiom,
% 2.43/2.62    (![A:$i,B:$i,C:$i]:
% 2.43/2.62     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.43/2.62       ( ![D:$i]:
% 2.43/2.62         ( ( r2_hidden @ D @ C ) <=>
% 2.43/2.62           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.43/2.62  thf('51', plain,
% 2.43/2.62      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.43/2.62         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 2.43/2.62          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.43/2.62          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.43/2.62      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.43/2.62  thf('52', plain,
% 2.43/2.62      (![X38 : $i, X39 : $i]:
% 2.43/2.62         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 2.43/2.62      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.43/2.62  thf('53', plain,
% 2.43/2.62      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.43/2.62         (((X5) = (k6_subset_1 @ X1 @ X2))
% 2.43/2.62          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.43/2.62          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.43/2.62      inference('demod', [status(thm)], ['51', '52'])).
% 2.43/2.62  thf(t4_boole, axiom,
% 2.43/2.62    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 2.43/2.62  thf('54', plain,
% 2.43/2.62      (![X16 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 2.43/2.62      inference('cnf', [status(esa)], [t4_boole])).
% 2.43/2.62  thf('55', plain,
% 2.43/2.62      (![X38 : $i, X39 : $i]:
% 2.43/2.62         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 2.43/2.62      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.43/2.62  thf('56', plain,
% 2.43/2.62      (![X16 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 2.43/2.62      inference('demod', [status(thm)], ['54', '55'])).
% 2.43/2.62  thf('57', plain,
% 2.43/2.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.43/2.62         (~ (r2_hidden @ X4 @ X3)
% 2.43/2.62          | ~ (r2_hidden @ X4 @ X2)
% 2.43/2.62          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 2.43/2.62      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.43/2.62  thf('58', plain,
% 2.43/2.62      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.43/2.62         (~ (r2_hidden @ X4 @ X2)
% 2.43/2.62          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 2.43/2.62      inference('simplify', [status(thm)], ['57'])).
% 2.43/2.62  thf('59', plain,
% 2.43/2.62      (![X38 : $i, X39 : $i]:
% 2.43/2.62         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 2.43/2.62      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.43/2.62  thf('60', plain,
% 2.43/2.62      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.43/2.62         (~ (r2_hidden @ X4 @ X2)
% 2.43/2.62          | ~ (r2_hidden @ X4 @ (k6_subset_1 @ X1 @ X2)))),
% 2.43/2.62      inference('demod', [status(thm)], ['58', '59'])).
% 2.43/2.62  thf('61', plain,
% 2.43/2.62      (![X0 : $i, X1 : $i]:
% 2.43/2.62         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 2.43/2.62      inference('sup-', [status(thm)], ['56', '60'])).
% 2.43/2.62  thf('62', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.43/2.62      inference('condensation', [status(thm)], ['61'])).
% 2.43/2.62  thf('63', plain,
% 2.43/2.62      (![X0 : $i, X1 : $i]:
% 2.43/2.62         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.43/2.62          | ((X1) = (k6_subset_1 @ k1_xboole_0 @ X0)))),
% 2.43/2.62      inference('sup-', [status(thm)], ['53', '62'])).
% 2.43/2.62  thf('64', plain,
% 2.43/2.62      (![X16 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 2.43/2.62      inference('demod', [status(thm)], ['54', '55'])).
% 2.43/2.62  thf('65', plain,
% 2.43/2.62      (![X0 : $i, X1 : $i]:
% 2.43/2.62         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.43/2.62          | ((X1) = (k1_xboole_0)))),
% 2.43/2.62      inference('demod', [status(thm)], ['63', '64'])).
% 2.43/2.62  thf(commutativity_k2_tarski, axiom,
% 2.43/2.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.43/2.62  thf('66', plain,
% 2.43/2.62      (![X21 : $i, X22 : $i]:
% 2.43/2.62         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 2.43/2.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.43/2.62  thf(t12_setfam_1, axiom,
% 2.43/2.62    (![A:$i,B:$i]:
% 2.43/2.62     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.43/2.62  thf('67', plain,
% 2.43/2.62      (![X46 : $i, X47 : $i]:
% 2.43/2.62         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 2.43/2.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.43/2.62  thf('68', plain,
% 2.43/2.62      (![X0 : $i, X1 : $i]:
% 2.43/2.62         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 2.43/2.62      inference('sup+', [status(thm)], ['66', '67'])).
% 2.43/2.62  thf('69', plain,
% 2.43/2.62      (![X46 : $i, X47 : $i]:
% 2.43/2.62         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 2.43/2.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.43/2.62  thf('70', plain,
% 2.43/2.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.43/2.62      inference('sup+', [status(thm)], ['68', '69'])).
% 2.43/2.62  thf(t17_xboole_1, axiom,
% 2.43/2.62    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.43/2.62  thf('71', plain,
% 2.43/2.62      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 2.43/2.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.43/2.62  thf('72', plain,
% 2.43/2.62      (![X48 : $i, X50 : $i]:
% 2.43/2.62         ((m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X50)) | ~ (r1_tarski @ X48 @ X50))),
% 2.43/2.62      inference('cnf', [status(esa)], [t3_subset])).
% 2.43/2.62  thf('73', plain,
% 2.43/2.62      (![X0 : $i, X1 : $i]:
% 2.43/2.62         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.43/2.62      inference('sup-', [status(thm)], ['71', '72'])).
% 2.43/2.62  thf(l3_subset_1, axiom,
% 2.43/2.62    (![A:$i,B:$i]:
% 2.43/2.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.43/2.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 2.43/2.62  thf('74', plain,
% 2.43/2.62      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.43/2.62         (~ (r2_hidden @ X34 @ X35)
% 2.43/2.62          | (r2_hidden @ X34 @ X36)
% 2.43/2.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 2.43/2.62      inference('cnf', [status(esa)], [l3_subset_1])).
% 2.43/2.62  thf('75', plain,
% 2.43/2.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.43/2.62         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.43/2.62      inference('sup-', [status(thm)], ['73', '74'])).
% 2.43/2.62  thf('76', plain,
% 2.43/2.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.43/2.62         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X0))),
% 2.43/2.62      inference('sup-', [status(thm)], ['70', '75'])).
% 2.43/2.62  thf('77', plain,
% 2.43/2.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.43/2.62         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 2.43/2.62          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 2.43/2.62             X0))),
% 2.43/2.62      inference('sup-', [status(thm)], ['65', '76'])).
% 2.43/2.62  thf('78', plain,
% 2.43/2.62      (![X0 : $i, X1 : $i]:
% 2.43/2.62         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.43/2.62          | ((X1) = (k1_xboole_0)))),
% 2.43/2.62      inference('demod', [status(thm)], ['63', '64'])).
% 2.43/2.62  thf('79', plain,
% 2.43/2.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.43/2.62         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.43/2.62      inference('sup-', [status(thm)], ['73', '74'])).
% 2.43/2.62  thf('80', plain,
% 2.43/2.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.43/2.62         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 2.43/2.62          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 2.43/2.62             X1))),
% 2.43/2.62      inference('sup-', [status(thm)], ['78', '79'])).
% 2.43/2.62  thf('81', plain,
% 2.43/2.62      (![X0 : $i]:
% 2.43/2.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.62           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 2.43/2.62           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 2.43/2.63      inference('sup-', [status(thm)], ['40', '41'])).
% 2.43/2.63  thf('82', plain,
% 2.43/2.63      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.63             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 2.43/2.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.43/2.63      inference('split', [status(esa)], ['3'])).
% 2.43/2.63  thf('83', plain,
% 2.43/2.63      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.63          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 2.43/2.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.43/2.63      inference('sup+', [status(thm)], ['81', '82'])).
% 2.43/2.63  thf('84', plain,
% 2.43/2.63      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.43/2.63         (~ (r2_hidden @ X4 @ X2)
% 2.43/2.63          | ~ (r2_hidden @ X4 @ (k6_subset_1 @ X1 @ X2)))),
% 2.43/2.63      inference('demod', [status(thm)], ['58', '59'])).
% 2.43/2.63  thf('85', plain,
% 2.43/2.63      ((![X0 : $i]:
% 2.43/2.63          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B_1))
% 2.43/2.63           | ~ (r2_hidden @ X0 @ sk_B_1)))
% 2.43/2.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.43/2.63      inference('sup-', [status(thm)], ['83', '84'])).
% 2.43/2.63  thf('86', plain,
% 2.43/2.63      ((![X0 : $i, X1 : $i]:
% 2.43/2.63          (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ X1) = (k1_xboole_0))
% 2.43/2.63           | ~ (r2_hidden @ 
% 2.43/2.63                (sk_D @ (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ X1) @ 
% 2.43/2.63                 X0 @ k1_xboole_0) @ 
% 2.43/2.63                sk_B_1)))
% 2.43/2.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.43/2.63      inference('sup-', [status(thm)], ['80', '85'])).
% 2.43/2.63  thf('87', plain,
% 2.43/2.63      (((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ sk_B_1) = (k1_xboole_0))
% 2.43/2.63         | ((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 2.43/2.63             = (k1_xboole_0))))
% 2.43/2.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.43/2.63      inference('sup-', [status(thm)], ['77', '86'])).
% 2.43/2.63  thf('88', plain,
% 2.43/2.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.43/2.63      inference('sup+', [status(thm)], ['68', '69'])).
% 2.43/2.63  thf('89', plain,
% 2.43/2.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.43/2.63      inference('sup+', [status(thm)], ['68', '69'])).
% 2.43/2.63  thf('90', plain,
% 2.43/2.63      (((((k3_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))
% 2.43/2.63         | ((k3_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))
% 2.43/2.63             = (k1_xboole_0))))
% 2.43/2.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.43/2.63      inference('demod', [status(thm)], ['87', '88', '89'])).
% 2.43/2.63  thf('91', plain,
% 2.43/2.63      ((((k3_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 2.43/2.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.43/2.63      inference('simplify', [status(thm)], ['90'])).
% 2.43/2.63  thf(t51_xboole_1, axiom,
% 2.43/2.63    (![A:$i,B:$i]:
% 2.43/2.63     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 2.43/2.63       ( A ) ))).
% 2.43/2.63  thf('92', plain,
% 2.43/2.63      (![X17 : $i, X18 : $i]:
% 2.43/2.63         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 2.43/2.63           = (X17))),
% 2.43/2.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.43/2.63  thf('93', plain,
% 2.43/2.63      (![X38 : $i, X39 : $i]:
% 2.43/2.63         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 2.43/2.63      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.43/2.63  thf('94', plain,
% 2.43/2.63      (![X17 : $i, X18 : $i]:
% 2.43/2.63         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k6_subset_1 @ X17 @ X18))
% 2.43/2.63           = (X17))),
% 2.43/2.63      inference('demod', [status(thm)], ['92', '93'])).
% 2.43/2.63  thf('95', plain,
% 2.43/2.63      ((((k2_xboole_0 @ k1_xboole_0 @ 
% 2.43/2.63          (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))) = (sk_B_1)))
% 2.43/2.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.43/2.63      inference('sup+', [status(thm)], ['91', '94'])).
% 2.43/2.63  thf('96', plain,
% 2.43/2.63      (((k1_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.63         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 2.43/2.63      inference('demod', [status(thm)], ['17', '18', '23'])).
% 2.43/2.63  thf('97', plain,
% 2.43/2.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.43/2.63      inference('sup+', [status(thm)], ['68', '69'])).
% 2.43/2.63  thf('98', plain,
% 2.43/2.63      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 2.43/2.63      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.43/2.63  thf(t3_xboole_1, axiom,
% 2.43/2.63    (![A:$i]:
% 2.43/2.63     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.43/2.63  thf('99', plain,
% 2.43/2.63      (![X15 : $i]:
% 2.43/2.63         (((X15) = (k1_xboole_0)) | ~ (r1_tarski @ X15 @ k1_xboole_0))),
% 2.43/2.63      inference('cnf', [status(esa)], [t3_xboole_1])).
% 2.43/2.63  thf('100', plain,
% 2.43/2.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.43/2.63      inference('sup-', [status(thm)], ['98', '99'])).
% 2.43/2.63  thf('101', plain,
% 2.43/2.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.43/2.63      inference('sup+', [status(thm)], ['97', '100'])).
% 2.43/2.63  thf(t100_xboole_1, axiom,
% 2.43/2.63    (![A:$i,B:$i]:
% 2.43/2.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.43/2.63  thf('102', plain,
% 2.43/2.63      (![X10 : $i, X11 : $i]:
% 2.43/2.63         ((k4_xboole_0 @ X10 @ X11)
% 2.43/2.63           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 2.43/2.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.43/2.63  thf('103', plain,
% 2.43/2.63      (![X38 : $i, X39 : $i]:
% 2.43/2.63         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 2.43/2.63      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.43/2.63  thf('104', plain,
% 2.43/2.63      (![X10 : $i, X11 : $i]:
% 2.43/2.63         ((k6_subset_1 @ X10 @ X11)
% 2.43/2.63           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 2.43/2.63      inference('demod', [status(thm)], ['102', '103'])).
% 2.43/2.63  thf('105', plain,
% 2.43/2.63      (![X0 : $i]:
% 2.43/2.63         ((k6_subset_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.43/2.63      inference('sup+', [status(thm)], ['101', '104'])).
% 2.43/2.63  thf('106', plain,
% 2.43/2.63      (![X16 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 2.43/2.63      inference('demod', [status(thm)], ['54', '55'])).
% 2.43/2.63  thf(t98_xboole_1, axiom,
% 2.43/2.63    (![A:$i,B:$i]:
% 2.43/2.63     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.43/2.63  thf('107', plain,
% 2.43/2.63      (![X19 : $i, X20 : $i]:
% 2.43/2.63         ((k2_xboole_0 @ X19 @ X20)
% 2.43/2.63           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 2.43/2.63      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.43/2.63  thf('108', plain,
% 2.43/2.63      (![X38 : $i, X39 : $i]:
% 2.43/2.63         ((k6_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))),
% 2.43/2.63      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.43/2.63  thf('109', plain,
% 2.43/2.63      (![X19 : $i, X20 : $i]:
% 2.43/2.63         ((k2_xboole_0 @ X19 @ X20)
% 2.43/2.63           = (k5_xboole_0 @ X19 @ (k6_subset_1 @ X20 @ X19)))),
% 2.43/2.63      inference('demod', [status(thm)], ['107', '108'])).
% 2.43/2.63  thf('110', plain,
% 2.43/2.63      (![X0 : $i]:
% 2.43/2.63         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.43/2.63      inference('sup+', [status(thm)], ['106', '109'])).
% 2.43/2.63  thf(t1_boole, axiom,
% 2.43/2.63    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.43/2.63  thf('111', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 2.43/2.63      inference('cnf', [status(esa)], [t1_boole])).
% 2.43/2.63  thf('112', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.43/2.63      inference('sup+', [status(thm)], ['110', '111'])).
% 2.43/2.63  thf('113', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 2.43/2.63      inference('demod', [status(thm)], ['105', '112'])).
% 2.43/2.63  thf('114', plain,
% 2.43/2.63      (![X17 : $i, X18 : $i]:
% 2.43/2.63         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k6_subset_1 @ X17 @ X18))
% 2.43/2.63           = (X17))),
% 2.43/2.63      inference('demod', [status(thm)], ['92', '93'])).
% 2.43/2.63  thf('115', plain,
% 2.43/2.63      (![X0 : $i]:
% 2.43/2.63         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (X0))),
% 2.43/2.63      inference('sup+', [status(thm)], ['113', '114'])).
% 2.43/2.63  thf('116', plain,
% 2.43/2.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.43/2.63      inference('sup+', [status(thm)], ['97', '100'])).
% 2.43/2.63  thf('117', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.43/2.63      inference('demod', [status(thm)], ['115', '116'])).
% 2.43/2.63  thf('118', plain,
% 2.43/2.63      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 2.43/2.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.43/2.63      inference('demod', [status(thm)], ['95', '96', '117'])).
% 2.43/2.63  thf('119', plain,
% 2.43/2.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.43/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.63  thf(fc9_tops_1, axiom,
% 2.43/2.63    (![A:$i,B:$i]:
% 2.43/2.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 2.43/2.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.43/2.63       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 2.43/2.63  thf('120', plain,
% 2.43/2.63      (![X55 : $i, X56 : $i]:
% 2.43/2.63         (~ (l1_pre_topc @ X55)
% 2.43/2.63          | ~ (v2_pre_topc @ X55)
% 2.43/2.63          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 2.43/2.63          | (v3_pre_topc @ (k1_tops_1 @ X55 @ X56) @ X55))),
% 2.43/2.63      inference('cnf', [status(esa)], [fc9_tops_1])).
% 2.43/2.63  thf('121', plain,
% 2.43/2.63      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 2.43/2.63        | ~ (v2_pre_topc @ sk_A)
% 2.43/2.63        | ~ (l1_pre_topc @ sk_A))),
% 2.43/2.63      inference('sup-', [status(thm)], ['119', '120'])).
% 2.43/2.63  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 2.43/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.63  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 2.43/2.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.63  thf('124', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 2.43/2.63      inference('demod', [status(thm)], ['121', '122', '123'])).
% 2.43/2.63  thf('125', plain,
% 2.43/2.63      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 2.43/2.63         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.63                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.63                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.43/2.63      inference('sup+', [status(thm)], ['118', '124'])).
% 2.43/2.63  thf('126', plain,
% 2.43/2.63      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.43/2.63      inference('split', [status(esa)], ['0'])).
% 2.43/2.63  thf('127', plain,
% 2.43/2.63      (~
% 2.43/2.63       (((k2_tops_1 @ sk_A @ sk_B_1)
% 2.43/2.63          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.43/2.63             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 2.43/2.63       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.43/2.63      inference('sup-', [status(thm)], ['125', '126'])).
% 2.43/2.63  thf('128', plain, ($false),
% 2.43/2.63      inference('sat_resolution*', [status(thm)], ['1', '49', '50', '127'])).
% 2.43/2.63  
% 2.43/2.63  % SZS output end Refutation
% 2.43/2.63  
% 2.49/2.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
