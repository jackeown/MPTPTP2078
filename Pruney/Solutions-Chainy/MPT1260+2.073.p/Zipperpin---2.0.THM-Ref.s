%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RzQL06sOw1

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:34 EST 2020

% Result     : Theorem 23.32s
% Output     : Refutation 23.32s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 535 expanded)
%              Number of leaves         :   36 ( 166 expanded)
%              Depth                    :   14
%              Number of atoms          : 1583 (7259 expanded)
%              Number of equality atoms :   91 ( 340 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v3_pre_topc @ X44 @ X45 )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ( r1_tarski @ X44 @ ( k1_tops_1 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
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
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( ( k1_tops_1 @ X50 @ X49 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X50 ) @ X49 @ ( k2_tops_1 @ X50 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k7_subset_1 @ X28 @ X27 @ X29 )
        = ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k2_tops_1 @ X43 @ X42 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k2_pre_topc @ X43 @ X42 ) @ ( k1_tops_1 @ X43 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X16 @ X15 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('50',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( ( k2_pre_topc @ X48 @ X47 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X48 ) @ X47 @ ( k2_tops_1 @ X48 @ X47 ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k7_subset_1 @ X28 @ X27 @ X29 )
        = ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('60',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('63',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k7_subset_1 @ X31 @ X32 @ X30 )
        = ( k9_subset_1 @ X31 @ X32 @ ( k3_subset_1 @ X31 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('71',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k7_subset_1 @ X28 @ X27 @ X29 )
        = ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('75',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('77',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k9_subset_1 @ X20 @ X19 @ X19 )
        = X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,
    ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['58','79'])).

thf('81',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('82',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('83',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('84',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k4_subset_1 @ X25 @ X24 @ X26 )
        = ( k2_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('88',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('89',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('90',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('92',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X23 @ ( k3_subset_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('95',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['93','96','97'])).

thf('99',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['88','98'])).

thf('100',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('101',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['81','101'])).

thf('103',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('104',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('105',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['81','101'])).

thf('106',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['80','102','103','104','105'])).

thf('107',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('108',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('110',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X40 @ X41 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('111',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['108','114'])).

thf('116',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('117',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','38','39','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RzQL06sOw1
% 0.13/0.36  % Computer   : n005.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 09:50:18 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 23.32/23.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 23.32/23.51  % Solved by: fo/fo7.sh
% 23.32/23.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 23.32/23.51  % done 14573 iterations in 23.039s
% 23.32/23.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 23.32/23.51  % SZS output start Refutation
% 23.32/23.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 23.32/23.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 23.32/23.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 23.32/23.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 23.32/23.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 23.32/23.51  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 23.32/23.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 23.32/23.51  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 23.32/23.51  thf(sk_A_type, type, sk_A: $i).
% 23.32/23.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 23.32/23.51  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 23.32/23.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 23.32/23.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 23.32/23.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 23.32/23.51  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 23.32/23.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 23.32/23.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 23.32/23.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 23.32/23.51  thf(t76_tops_1, conjecture,
% 23.32/23.51    (![A:$i]:
% 23.32/23.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 23.32/23.51       ( ![B:$i]:
% 23.32/23.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.32/23.51           ( ( v3_pre_topc @ B @ A ) <=>
% 23.32/23.51             ( ( k2_tops_1 @ A @ B ) =
% 23.32/23.51               ( k7_subset_1 @
% 23.32/23.51                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 23.32/23.51  thf(zf_stmt_0, negated_conjecture,
% 23.32/23.51    (~( ![A:$i]:
% 23.32/23.51        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 23.32/23.51          ( ![B:$i]:
% 23.32/23.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.32/23.51              ( ( v3_pre_topc @ B @ A ) <=>
% 23.32/23.51                ( ( k2_tops_1 @ A @ B ) =
% 23.32/23.51                  ( k7_subset_1 @
% 23.32/23.51                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 23.32/23.51    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 23.32/23.51  thf('0', plain,
% 23.32/23.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 23.32/23.51        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf('1', plain,
% 23.32/23.51      (~
% 23.32/23.51       (((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 23.32/23.51       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 23.32/23.51      inference('split', [status(esa)], ['0'])).
% 23.32/23.51  thf('2', plain,
% 23.32/23.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf('3', plain,
% 23.32/23.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 23.32/23.51        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf('4', plain,
% 23.32/23.51      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 23.32/23.51      inference('split', [status(esa)], ['3'])).
% 23.32/23.51  thf('5', plain,
% 23.32/23.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf(t56_tops_1, axiom,
% 23.32/23.51    (![A:$i]:
% 23.32/23.51     ( ( l1_pre_topc @ A ) =>
% 23.32/23.51       ( ![B:$i]:
% 23.32/23.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.32/23.51           ( ![C:$i]:
% 23.32/23.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.32/23.51               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 23.32/23.51                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 23.32/23.51  thf('6', plain,
% 23.32/23.51      (![X44 : $i, X45 : $i, X46 : $i]:
% 23.32/23.51         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 23.32/23.51          | ~ (v3_pre_topc @ X44 @ X45)
% 23.32/23.51          | ~ (r1_tarski @ X44 @ X46)
% 23.32/23.51          | (r1_tarski @ X44 @ (k1_tops_1 @ X45 @ X46))
% 23.32/23.51          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 23.32/23.51          | ~ (l1_pre_topc @ X45))),
% 23.32/23.51      inference('cnf', [status(esa)], [t56_tops_1])).
% 23.32/23.51  thf('7', plain,
% 23.32/23.51      (![X0 : $i]:
% 23.32/23.51         (~ (l1_pre_topc @ sk_A)
% 23.32/23.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 23.32/23.51          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 23.32/23.51          | ~ (r1_tarski @ sk_B_1 @ X0)
% 23.32/23.51          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 23.32/23.51      inference('sup-', [status(thm)], ['5', '6'])).
% 23.32/23.51  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf('9', plain,
% 23.32/23.51      (![X0 : $i]:
% 23.32/23.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 23.32/23.51          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 23.32/23.51          | ~ (r1_tarski @ sk_B_1 @ X0)
% 23.32/23.51          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 23.32/23.51      inference('demod', [status(thm)], ['7', '8'])).
% 23.32/23.51  thf('10', plain,
% 23.32/23.51      ((![X0 : $i]:
% 23.32/23.51          (~ (r1_tarski @ sk_B_1 @ X0)
% 23.32/23.51           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 23.32/23.51           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 23.32/23.51         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 23.32/23.51      inference('sup-', [status(thm)], ['4', '9'])).
% 23.32/23.51  thf('11', plain,
% 23.32/23.51      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 23.32/23.51         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 23.32/23.51         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 23.32/23.51      inference('sup-', [status(thm)], ['2', '10'])).
% 23.32/23.51  thf(d10_xboole_0, axiom,
% 23.32/23.51    (![A:$i,B:$i]:
% 23.32/23.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 23.32/23.51  thf('12', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 23.32/23.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 23.32/23.51  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 23.32/23.51      inference('simplify', [status(thm)], ['12'])).
% 23.32/23.51  thf('14', plain,
% 23.32/23.51      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 23.32/23.51         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 23.32/23.51      inference('demod', [status(thm)], ['11', '13'])).
% 23.32/23.51  thf('15', plain,
% 23.32/23.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf(t74_tops_1, axiom,
% 23.32/23.51    (![A:$i]:
% 23.32/23.51     ( ( l1_pre_topc @ A ) =>
% 23.32/23.51       ( ![B:$i]:
% 23.32/23.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.32/23.51           ( ( k1_tops_1 @ A @ B ) =
% 23.32/23.51             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 23.32/23.51  thf('16', plain,
% 23.32/23.51      (![X49 : $i, X50 : $i]:
% 23.32/23.51         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 23.32/23.51          | ((k1_tops_1 @ X50 @ X49)
% 23.32/23.51              = (k7_subset_1 @ (u1_struct_0 @ X50) @ X49 @ 
% 23.32/23.51                 (k2_tops_1 @ X50 @ X49)))
% 23.32/23.51          | ~ (l1_pre_topc @ X50))),
% 23.32/23.51      inference('cnf', [status(esa)], [t74_tops_1])).
% 23.32/23.51  thf('17', plain,
% 23.32/23.51      ((~ (l1_pre_topc @ sk_A)
% 23.32/23.51        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 23.32/23.51               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 23.32/23.51      inference('sup-', [status(thm)], ['15', '16'])).
% 23.32/23.51  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf('19', plain,
% 23.32/23.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf(redefinition_k7_subset_1, axiom,
% 23.32/23.51    (![A:$i,B:$i,C:$i]:
% 23.32/23.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 23.32/23.51       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 23.32/23.51  thf('20', plain,
% 23.32/23.51      (![X27 : $i, X28 : $i, X29 : $i]:
% 23.32/23.51         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 23.32/23.51          | ((k7_subset_1 @ X28 @ X27 @ X29) = (k4_xboole_0 @ X27 @ X29)))),
% 23.32/23.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 23.32/23.51  thf('21', plain,
% 23.32/23.51      (![X0 : $i]:
% 23.32/23.51         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 23.32/23.51           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 23.32/23.51      inference('sup-', [status(thm)], ['19', '20'])).
% 23.32/23.51  thf('22', plain,
% 23.32/23.51      (((k1_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 23.32/23.51      inference('demod', [status(thm)], ['17', '18', '21'])).
% 23.32/23.51  thf(t36_xboole_1, axiom,
% 23.32/23.51    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 23.32/23.51  thf('23', plain,
% 23.32/23.51      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 23.32/23.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 23.32/23.51  thf('24', plain,
% 23.32/23.51      (![X0 : $i, X2 : $i]:
% 23.32/23.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 23.32/23.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 23.32/23.51  thf('25', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]:
% 23.32/23.51         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 23.32/23.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 23.32/23.51      inference('sup-', [status(thm)], ['23', '24'])).
% 23.32/23.51  thf('26', plain,
% 23.32/23.51      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 23.32/23.51        | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 23.32/23.51      inference('sup-', [status(thm)], ['22', '25'])).
% 23.32/23.51  thf('27', plain,
% 23.32/23.51      (((k1_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 23.32/23.51      inference('demod', [status(thm)], ['17', '18', '21'])).
% 23.32/23.51  thf('28', plain,
% 23.32/23.51      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 23.32/23.51        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 23.32/23.51      inference('demod', [status(thm)], ['26', '27'])).
% 23.32/23.51  thf('29', plain,
% 23.32/23.51      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 23.32/23.51         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 23.32/23.51      inference('sup-', [status(thm)], ['14', '28'])).
% 23.32/23.51  thf('30', plain,
% 23.32/23.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf(l78_tops_1, axiom,
% 23.32/23.51    (![A:$i]:
% 23.32/23.51     ( ( l1_pre_topc @ A ) =>
% 23.32/23.51       ( ![B:$i]:
% 23.32/23.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.32/23.51           ( ( k2_tops_1 @ A @ B ) =
% 23.32/23.51             ( k7_subset_1 @
% 23.32/23.51               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 23.32/23.51               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 23.32/23.51  thf('31', plain,
% 23.32/23.51      (![X42 : $i, X43 : $i]:
% 23.32/23.51         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 23.32/23.51          | ((k2_tops_1 @ X43 @ X42)
% 23.32/23.51              = (k7_subset_1 @ (u1_struct_0 @ X43) @ 
% 23.32/23.51                 (k2_pre_topc @ X43 @ X42) @ (k1_tops_1 @ X43 @ X42)))
% 23.32/23.51          | ~ (l1_pre_topc @ X43))),
% 23.32/23.51      inference('cnf', [status(esa)], [l78_tops_1])).
% 23.32/23.51  thf('32', plain,
% 23.32/23.51      ((~ (l1_pre_topc @ sk_A)
% 23.32/23.51        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 23.32/23.51      inference('sup-', [status(thm)], ['30', '31'])).
% 23.32/23.51  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf('34', plain,
% 23.32/23.51      (((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 23.32/23.51      inference('demod', [status(thm)], ['32', '33'])).
% 23.32/23.51  thf('35', plain,
% 23.32/23.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 23.32/23.51         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 23.32/23.51      inference('sup+', [status(thm)], ['29', '34'])).
% 23.32/23.51  thf('36', plain,
% 23.32/23.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 23.32/23.51         <= (~
% 23.32/23.51             (((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 23.32/23.51      inference('split', [status(esa)], ['0'])).
% 23.32/23.51  thf('37', plain,
% 23.32/23.51      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 23.32/23.51         <= (~
% 23.32/23.51             (((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 23.32/23.51             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 23.32/23.51      inference('sup-', [status(thm)], ['35', '36'])).
% 23.32/23.51  thf('38', plain,
% 23.32/23.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 23.32/23.51       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 23.32/23.51      inference('simplify', [status(thm)], ['37'])).
% 23.32/23.51  thf('39', plain,
% 23.32/23.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 23.32/23.51       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 23.32/23.51      inference('split', [status(esa)], ['3'])).
% 23.32/23.51  thf('40', plain,
% 23.32/23.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf(dt_k2_tops_1, axiom,
% 23.32/23.51    (![A:$i,B:$i]:
% 23.32/23.51     ( ( ( l1_pre_topc @ A ) & 
% 23.32/23.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 23.32/23.51       ( m1_subset_1 @
% 23.32/23.51         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 23.32/23.51  thf('41', plain,
% 23.32/23.51      (![X38 : $i, X39 : $i]:
% 23.32/23.51         (~ (l1_pre_topc @ X38)
% 23.32/23.51          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 23.32/23.51          | (m1_subset_1 @ (k2_tops_1 @ X38 @ X39) @ 
% 23.32/23.51             (k1_zfmisc_1 @ (u1_struct_0 @ X38))))),
% 23.32/23.51      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 23.32/23.51  thf('42', plain,
% 23.32/23.51      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 23.32/23.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 23.32/23.51        | ~ (l1_pre_topc @ sk_A))),
% 23.32/23.51      inference('sup-', [status(thm)], ['40', '41'])).
% 23.32/23.51  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf('44', plain,
% 23.32/23.51      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 23.32/23.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.32/23.51      inference('demod', [status(thm)], ['42', '43'])).
% 23.32/23.51  thf('45', plain,
% 23.32/23.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf(dt_k4_subset_1, axiom,
% 23.32/23.51    (![A:$i,B:$i,C:$i]:
% 23.32/23.51     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 23.32/23.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 23.32/23.51       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 23.32/23.51  thf('46', plain,
% 23.32/23.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 23.32/23.51         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 23.32/23.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 23.32/23.51          | (m1_subset_1 @ (k4_subset_1 @ X16 @ X15 @ X17) @ 
% 23.32/23.51             (k1_zfmisc_1 @ X16)))),
% 23.32/23.51      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 23.32/23.51  thf('47', plain,
% 23.32/23.51      (![X0 : $i]:
% 23.32/23.51         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 23.32/23.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 23.32/23.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 23.32/23.51      inference('sup-', [status(thm)], ['45', '46'])).
% 23.32/23.51  thf('48', plain,
% 23.32/23.51      ((m1_subset_1 @ 
% 23.32/23.51        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 23.32/23.51         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 23.32/23.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.32/23.51      inference('sup-', [status(thm)], ['44', '47'])).
% 23.32/23.51  thf('49', plain,
% 23.32/23.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf(t65_tops_1, axiom,
% 23.32/23.51    (![A:$i]:
% 23.32/23.51     ( ( l1_pre_topc @ A ) =>
% 23.32/23.51       ( ![B:$i]:
% 23.32/23.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.32/23.51           ( ( k2_pre_topc @ A @ B ) =
% 23.32/23.51             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 23.32/23.51  thf('50', plain,
% 23.32/23.51      (![X47 : $i, X48 : $i]:
% 23.32/23.51         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 23.32/23.51          | ((k2_pre_topc @ X48 @ X47)
% 23.32/23.51              = (k4_subset_1 @ (u1_struct_0 @ X48) @ X47 @ 
% 23.32/23.51                 (k2_tops_1 @ X48 @ X47)))
% 23.32/23.51          | ~ (l1_pre_topc @ X48))),
% 23.32/23.51      inference('cnf', [status(esa)], [t65_tops_1])).
% 23.32/23.51  thf('51', plain,
% 23.32/23.51      ((~ (l1_pre_topc @ sk_A)
% 23.32/23.51        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 23.32/23.51            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 23.32/23.51               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 23.32/23.51      inference('sup-', [status(thm)], ['49', '50'])).
% 23.32/23.51  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf('53', plain,
% 23.32/23.51      (((k2_pre_topc @ sk_A @ sk_B_1)
% 23.32/23.51         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 23.32/23.51            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 23.32/23.51      inference('demod', [status(thm)], ['51', '52'])).
% 23.32/23.51  thf('54', plain,
% 23.32/23.51      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 23.32/23.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.32/23.51      inference('demod', [status(thm)], ['48', '53'])).
% 23.32/23.51  thf('55', plain,
% 23.32/23.51      (![X27 : $i, X28 : $i, X29 : $i]:
% 23.32/23.51         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 23.32/23.51          | ((k7_subset_1 @ X28 @ X27 @ X29) = (k4_xboole_0 @ X27 @ X29)))),
% 23.32/23.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 23.32/23.51  thf('56', plain,
% 23.32/23.51      (![X0 : $i]:
% 23.32/23.51         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 23.32/23.51           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 23.32/23.51      inference('sup-', [status(thm)], ['54', '55'])).
% 23.32/23.51  thf('57', plain,
% 23.32/23.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 23.32/23.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 23.32/23.51      inference('split', [status(esa)], ['3'])).
% 23.32/23.51  thf('58', plain,
% 23.32/23.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 23.32/23.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 23.32/23.51      inference('sup+', [status(thm)], ['56', '57'])).
% 23.32/23.51  thf('59', plain,
% 23.32/23.51      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 23.32/23.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 23.32/23.51  thf(t3_subset, axiom,
% 23.32/23.51    (![A:$i,B:$i]:
% 23.32/23.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 23.32/23.51  thf('60', plain,
% 23.32/23.51      (![X35 : $i, X37 : $i]:
% 23.32/23.51         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 23.32/23.51      inference('cnf', [status(esa)], [t3_subset])).
% 23.32/23.51  thf('61', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]:
% 23.32/23.51         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 23.32/23.51      inference('sup-', [status(thm)], ['59', '60'])).
% 23.32/23.51  thf('62', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]:
% 23.32/23.51         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 23.32/23.51      inference('sup-', [status(thm)], ['59', '60'])).
% 23.32/23.51  thf(t32_subset_1, axiom,
% 23.32/23.51    (![A:$i,B:$i]:
% 23.32/23.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 23.32/23.51       ( ![C:$i]:
% 23.32/23.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 23.32/23.51           ( ( k7_subset_1 @ A @ B @ C ) =
% 23.32/23.51             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 23.32/23.51  thf('63', plain,
% 23.32/23.51      (![X30 : $i, X31 : $i, X32 : $i]:
% 23.32/23.51         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 23.32/23.51          | ((k7_subset_1 @ X31 @ X32 @ X30)
% 23.32/23.51              = (k9_subset_1 @ X31 @ X32 @ (k3_subset_1 @ X31 @ X30)))
% 23.32/23.51          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 23.32/23.51      inference('cnf', [status(esa)], [t32_subset_1])).
% 23.32/23.51  thf('64', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.32/23.51         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 23.32/23.51          | ((k7_subset_1 @ X0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 23.32/23.51              = (k9_subset_1 @ X0 @ X2 @ 
% 23.32/23.51                 (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))))),
% 23.32/23.51      inference('sup-', [status(thm)], ['62', '63'])).
% 23.32/23.51  thf('65', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]:
% 23.32/23.51         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 23.32/23.51      inference('sup-', [status(thm)], ['59', '60'])).
% 23.32/23.51  thf(d5_subset_1, axiom,
% 23.32/23.51    (![A:$i,B:$i]:
% 23.32/23.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 23.32/23.51       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 23.32/23.51  thf('66', plain,
% 23.32/23.51      (![X11 : $i, X12 : $i]:
% 23.32/23.51         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 23.32/23.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 23.32/23.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 23.32/23.51  thf('67', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]:
% 23.32/23.51         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 23.32/23.51           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 23.32/23.51      inference('sup-', [status(thm)], ['65', '66'])).
% 23.32/23.51  thf('68', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.32/23.51         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 23.32/23.51          | ((k7_subset_1 @ X0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 23.32/23.51              = (k9_subset_1 @ X0 @ X2 @ 
% 23.32/23.51                 (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))))),
% 23.32/23.51      inference('demod', [status(thm)], ['64', '67'])).
% 23.32/23.51  thf('69', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.32/23.51         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2))
% 23.32/23.51           = (k9_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 23.32/23.51              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X2))))),
% 23.32/23.51      inference('sup-', [status(thm)], ['61', '68'])).
% 23.32/23.51  thf('70', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]:
% 23.32/23.51         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 23.32/23.51      inference('sup-', [status(thm)], ['59', '60'])).
% 23.32/23.51  thf('71', plain,
% 23.32/23.51      (![X27 : $i, X28 : $i, X29 : $i]:
% 23.32/23.51         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 23.32/23.51          | ((k7_subset_1 @ X28 @ X27 @ X29) = (k4_xboole_0 @ X27 @ X29)))),
% 23.32/23.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 23.32/23.51  thf('72', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.32/23.51         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 23.32/23.51           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 23.32/23.51      inference('sup-', [status(thm)], ['70', '71'])).
% 23.32/23.51  thf('73', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.32/23.51         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2))
% 23.32/23.51           = (k9_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 23.32/23.51              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X2))))),
% 23.32/23.51      inference('demod', [status(thm)], ['69', '72'])).
% 23.32/23.51  thf('74', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 23.32/23.51      inference('simplify', [status(thm)], ['12'])).
% 23.32/23.51  thf('75', plain,
% 23.32/23.51      (![X35 : $i, X37 : $i]:
% 23.32/23.51         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 23.32/23.51      inference('cnf', [status(esa)], [t3_subset])).
% 23.32/23.51  thf('76', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 23.32/23.51      inference('sup-', [status(thm)], ['74', '75'])).
% 23.32/23.51  thf(idempotence_k9_subset_1, axiom,
% 23.32/23.51    (![A:$i,B:$i,C:$i]:
% 23.32/23.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 23.32/23.51       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 23.32/23.51  thf('77', plain,
% 23.32/23.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 23.32/23.51         (((k9_subset_1 @ X20 @ X19 @ X19) = (X19))
% 23.32/23.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 23.32/23.51      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 23.32/23.51  thf('78', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 23.32/23.51      inference('sup-', [status(thm)], ['76', '77'])).
% 23.32/23.51  thf('79', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]:
% 23.32/23.51         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 23.32/23.51           (k4_xboole_0 @ X1 @ X0))
% 23.32/23.51           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 23.32/23.51      inference('sup+', [status(thm)], ['73', '78'])).
% 23.32/23.51  thf('80', plain,
% 23.32/23.51      ((((k4_xboole_0 @ 
% 23.32/23.51          (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 23.32/23.51           (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 23.32/23.51          (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 23.32/23.51          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 23.32/23.51             (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))
% 23.32/23.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 23.32/23.51      inference('sup+', [status(thm)], ['58', '79'])).
% 23.32/23.51  thf('81', plain,
% 23.32/23.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 23.32/23.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 23.32/23.51      inference('sup+', [status(thm)], ['56', '57'])).
% 23.32/23.51  thf('82', plain,
% 23.32/23.51      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 23.32/23.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.32/23.51      inference('demod', [status(thm)], ['42', '43'])).
% 23.32/23.51  thf('83', plain,
% 23.32/23.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf(redefinition_k4_subset_1, axiom,
% 23.32/23.51    (![A:$i,B:$i,C:$i]:
% 23.32/23.51     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 23.32/23.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 23.32/23.51       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 23.32/23.51  thf('84', plain,
% 23.32/23.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 23.32/23.51         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 23.32/23.51          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25))
% 23.32/23.51          | ((k4_subset_1 @ X25 @ X24 @ X26) = (k2_xboole_0 @ X24 @ X26)))),
% 23.32/23.51      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 23.32/23.51  thf('85', plain,
% 23.32/23.51      (![X0 : $i]:
% 23.32/23.51         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 23.32/23.51            = (k2_xboole_0 @ sk_B_1 @ X0))
% 23.32/23.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 23.32/23.51      inference('sup-', [status(thm)], ['83', '84'])).
% 23.32/23.51  thf('86', plain,
% 23.32/23.51      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 23.32/23.51         (k2_tops_1 @ sk_A @ sk_B_1))
% 23.32/23.51         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 23.32/23.51      inference('sup-', [status(thm)], ['82', '85'])).
% 23.32/23.51  thf('87', plain,
% 23.32/23.51      (((k2_pre_topc @ sk_A @ sk_B_1)
% 23.32/23.51         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 23.32/23.51            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 23.32/23.51      inference('demod', [status(thm)], ['51', '52'])).
% 23.32/23.51  thf('88', plain,
% 23.32/23.51      (((k2_pre_topc @ sk_A @ sk_B_1)
% 23.32/23.51         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 23.32/23.51      inference('sup+', [status(thm)], ['86', '87'])).
% 23.32/23.51  thf(t7_xboole_1, axiom,
% 23.32/23.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 23.32/23.51  thf('89', plain,
% 23.32/23.51      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 23.32/23.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 23.32/23.51  thf('90', plain,
% 23.32/23.51      (![X35 : $i, X37 : $i]:
% 23.32/23.51         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 23.32/23.51      inference('cnf', [status(esa)], [t3_subset])).
% 23.32/23.51  thf('91', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]:
% 23.32/23.51         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.32/23.51      inference('sup-', [status(thm)], ['89', '90'])).
% 23.32/23.51  thf(involutiveness_k3_subset_1, axiom,
% 23.32/23.51    (![A:$i,B:$i]:
% 23.32/23.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 23.32/23.51       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 23.32/23.51  thf('92', plain,
% 23.32/23.51      (![X22 : $i, X23 : $i]:
% 23.32/23.51         (((k3_subset_1 @ X23 @ (k3_subset_1 @ X23 @ X22)) = (X22))
% 23.32/23.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 23.32/23.51      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 23.32/23.51  thf('93', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]:
% 23.32/23.51         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 23.32/23.51           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 23.32/23.51      inference('sup-', [status(thm)], ['91', '92'])).
% 23.32/23.51  thf('94', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]:
% 23.32/23.51         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.32/23.51      inference('sup-', [status(thm)], ['89', '90'])).
% 23.32/23.51  thf('95', plain,
% 23.32/23.51      (![X11 : $i, X12 : $i]:
% 23.32/23.51         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 23.32/23.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 23.32/23.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 23.32/23.51  thf('96', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]:
% 23.32/23.51         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 23.32/23.51           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 23.32/23.51      inference('sup-', [status(thm)], ['94', '95'])).
% 23.32/23.51  thf('97', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]:
% 23.32/23.51         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 23.32/23.51           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 23.32/23.51      inference('sup-', [status(thm)], ['65', '66'])).
% 23.32/23.51  thf('98', plain,
% 23.32/23.51      (![X0 : $i, X1 : $i]:
% 23.32/23.51         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 23.32/23.51           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 23.32/23.51      inference('demod', [status(thm)], ['93', '96', '97'])).
% 23.32/23.51  thf('99', plain,
% 23.32/23.51      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 23.32/23.51         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 23.32/23.51      inference('sup+', [status(thm)], ['88', '98'])).
% 23.32/23.51  thf('100', plain,
% 23.32/23.51      (((k2_pre_topc @ sk_A @ sk_B_1)
% 23.32/23.51         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 23.32/23.51      inference('sup+', [status(thm)], ['86', '87'])).
% 23.32/23.51  thf('101', plain,
% 23.32/23.51      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 23.32/23.51         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 23.32/23.51      inference('demod', [status(thm)], ['99', '100'])).
% 23.32/23.51  thf('102', plain,
% 23.32/23.51      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 23.32/23.51          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 23.32/23.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 23.32/23.51      inference('sup+', [status(thm)], ['81', '101'])).
% 23.32/23.51  thf('103', plain,
% 23.32/23.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 23.32/23.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 23.32/23.51      inference('sup+', [status(thm)], ['56', '57'])).
% 23.32/23.51  thf('104', plain,
% 23.32/23.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 23.32/23.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 23.32/23.51      inference('sup+', [status(thm)], ['56', '57'])).
% 23.32/23.51  thf('105', plain,
% 23.32/23.51      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 23.32/23.51          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 23.32/23.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 23.32/23.51      inference('sup+', [status(thm)], ['81', '101'])).
% 23.32/23.51  thf('106', plain,
% 23.32/23.51      ((((k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 23.32/23.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 23.32/23.51      inference('demod', [status(thm)], ['80', '102', '103', '104', '105'])).
% 23.32/23.51  thf('107', plain,
% 23.32/23.51      (((k1_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 23.32/23.51      inference('demod', [status(thm)], ['17', '18', '21'])).
% 23.32/23.51  thf('108', plain,
% 23.32/23.51      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 23.32/23.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 23.32/23.51      inference('sup+', [status(thm)], ['106', '107'])).
% 23.32/23.51  thf('109', plain,
% 23.32/23.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf(fc9_tops_1, axiom,
% 23.32/23.51    (![A:$i,B:$i]:
% 23.32/23.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 23.32/23.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 23.32/23.51       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 23.32/23.51  thf('110', plain,
% 23.32/23.51      (![X40 : $i, X41 : $i]:
% 23.32/23.51         (~ (l1_pre_topc @ X40)
% 23.32/23.51          | ~ (v2_pre_topc @ X40)
% 23.32/23.51          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 23.32/23.51          | (v3_pre_topc @ (k1_tops_1 @ X40 @ X41) @ X40))),
% 23.32/23.51      inference('cnf', [status(esa)], [fc9_tops_1])).
% 23.32/23.51  thf('111', plain,
% 23.32/23.51      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 23.32/23.51        | ~ (v2_pre_topc @ sk_A)
% 23.32/23.51        | ~ (l1_pre_topc @ sk_A))),
% 23.32/23.51      inference('sup-', [status(thm)], ['109', '110'])).
% 23.32/23.51  thf('112', plain, ((v2_pre_topc @ sk_A)),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 23.32/23.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.32/23.51  thf('114', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 23.32/23.51      inference('demod', [status(thm)], ['111', '112', '113'])).
% 23.32/23.51  thf('115', plain,
% 23.32/23.51      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 23.32/23.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 23.32/23.51      inference('sup+', [status(thm)], ['108', '114'])).
% 23.32/23.51  thf('116', plain,
% 23.32/23.51      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 23.32/23.51      inference('split', [status(esa)], ['0'])).
% 23.32/23.51  thf('117', plain,
% 23.32/23.51      (~
% 23.32/23.51       (((k2_tops_1 @ sk_A @ sk_B_1)
% 23.32/23.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 23.32/23.51             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 23.32/23.51       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 23.32/23.51      inference('sup-', [status(thm)], ['115', '116'])).
% 23.32/23.51  thf('118', plain, ($false),
% 23.32/23.51      inference('sat_resolution*', [status(thm)], ['1', '38', '39', '117'])).
% 23.32/23.51  
% 23.32/23.51  % SZS output end Refutation
% 23.32/23.51  
% 23.32/23.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
