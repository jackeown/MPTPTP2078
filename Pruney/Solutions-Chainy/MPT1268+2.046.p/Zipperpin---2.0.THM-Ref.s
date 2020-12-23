%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AiizpXEh0Y

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:22 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 489 expanded)
%              Number of leaves         :   21 ( 134 expanded)
%              Depth                    :   18
%              Number of atoms          :  992 (7950 expanded)
%              Number of equality atoms :   46 ( 330 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t86_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( r1_tarski @ C @ B )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r1_tarski @ C @ B )
                      & ( v3_pre_topc @ C @ A ) )
                   => ( C = k1_xboole_0 ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    ! [X17: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X17 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X17 @ sk_A )
      | ~ ( r1_tarski @ X17 @ sk_B_1 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ! [X17: $i] :
        ( ( X17 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r1_tarski @ X17 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X7 @ X6 ) @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X17: $i] :
        ( ( X17 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r1_tarski @ X17 @ sk_B_1 ) )
   <= ! [X17: $i] :
        ( ( X17 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r1_tarski @ X17 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('16',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ! [X17: $i] :
        ( ( X17 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r1_tarski @ X17 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ! [X17: $i] :
        ( ( X17 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r1_tarski @ X17 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X4 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('20',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ! [X17: $i] :
        ( ( X17 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r1_tarski @ X17 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k1_tops_1 @ X16 @ X15 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) )
   <= ! [X17: $i] :
        ( ( X17 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r1_tarski @ X17 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ! [X17: $i] :
        ( ( X17 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X17 @ sk_A )
        | ~ ( r1_tarski @ X17 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ~ ! [X17: $i] :
          ( ( X17 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X17 @ sk_A )
          | ~ ( r1_tarski @ X17 @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['2','36'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ( r1_tarski @ ( k1_tops_1 @ X9 @ X8 ) @ ( k1_tops_1 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X11 )
      | ( ( k1_tops_1 @ X11 @ X12 )
        = X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('45',plain,
    ( ! [X11: $i,X12: $i] :
        ( ~ ( l1_pre_topc @ X11 )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
        | ~ ( v3_pre_topc @ X12 @ X11 )
        | ( ( k1_tops_1 @ X11 @ X12 )
          = X12 ) )
   <= ! [X11: $i,X12: $i] :
        ( ~ ( l1_pre_topc @ X11 )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
        | ~ ( v3_pre_topc @ X12 @ X11 )
        | ( ( k1_tops_1 @ X11 @ X12 )
          = X12 ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X11 )
      | ( ( k1_tops_1 @ X11 @ X12 )
        = X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('48',plain,
    ( ! [X13: $i,X14: $i] :
        ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
        | ~ ( l1_pre_topc @ X14 )
        | ~ ( v2_pre_topc @ X14 ) )
   <= ! [X13: $i,X14: $i] :
        ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
        | ~ ( l1_pre_topc @ X14 )
        | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X13: $i,X14: $i] :
        ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
        | ~ ( l1_pre_topc @ X14 )
        | ~ ( v2_pre_topc @ X14 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ! [X13: $i,X14: $i] :
        ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
        | ~ ( l1_pre_topc @ X14 )
        | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ! [X11: $i,X12: $i] :
        ( ~ ( l1_pre_topc @ X11 )
        | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
        | ~ ( v3_pre_topc @ X12 @ X11 )
        | ( ( k1_tops_1 @ X11 @ X12 )
          = X12 ) )
    | ! [X13: $i,X14: $i] :
        ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
        | ~ ( l1_pre_topc @ X14 )
        | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(split,[status(esa)],['47'])).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X11 )
      | ( ( k1_tops_1 @ X11 @ X12 )
        = X12 ) ) ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X11 )
      | ( ( k1_tops_1 @ X11 @ X12 )
        = X12 ) ) ),
    inference(simpl_trail,[status(thm)],['45','54'])).

thf('56',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C )
        = sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C )
        = sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','58'])).

thf('60',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('61',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','34','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','34','35'])).

thf('63',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['59','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40','63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B_1 )
    | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','64'])).

thf('66',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['32'])).

thf('67',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('68',plain,(
    r1_tarski @ sk_C @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['4','34','67'])).

thf('69',plain,(
    r1_tarski @ sk_C @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['66','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tops_1 @ X15 @ X16 )
      | ( ( k1_tops_1 @ X16 @ X15 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('76',plain,(
    v2_tops_1 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','34'])).

thf('77',plain,(
    v2_tops_1 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['65','69','78'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('80',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('81',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['82'])).

thf('84',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['82'])).

thf('85',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','34','84'])).

thf('86',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['83','85'])).

thf('87',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AiizpXEh0Y
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:53:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 248 iterations in 0.167s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.62  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.41/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.62  thf(t86_tops_1, conjecture,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.62           ( ( v2_tops_1 @ B @ A ) <=>
% 0.41/0.62             ( ![C:$i]:
% 0.41/0.62               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.62                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.41/0.62                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i]:
% 0.41/0.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.62          ( ![B:$i]:
% 0.41/0.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.62              ( ( v2_tops_1 @ B @ A ) <=>
% 0.41/0.62                ( ![C:$i]:
% 0.41/0.62                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.62                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.41/0.62                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.41/0.62      inference('split', [status(esa)], ['1'])).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62          | ((X17) = (k1_xboole_0))
% 0.41/0.62          | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.41/0.62          | ~ (r1_tarski @ X17 @ sk_B_1)
% 0.41/0.62          | (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      (((v2_tops_1 @ sk_B_1 @ sk_A)) | 
% 0.41/0.62       (![X17 : $i]:
% 0.41/0.62          (((X17) = (k1_xboole_0))
% 0.41/0.62           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62           | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.41/0.62           | ~ (r1_tarski @ X17 @ sk_B_1)))),
% 0.41/0.62      inference('split', [status(esa)], ['3'])).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t44_tops_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( l1_pre_topc @ A ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.62           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      (![X6 : $i, X7 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.41/0.62          | (r1_tarski @ (k1_tops_1 @ X7 @ X6) @ X6)
% 0.41/0.62          | ~ (l1_pre_topc @ X7))),
% 0.41/0.62      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.62        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.62  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('9', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(dt_k1_tops_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( l1_pre_topc @ A ) & 
% 0.41/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.62       ( m1_subset_1 @
% 0.41/0.62         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i]:
% 0.41/0.62         (~ (l1_pre_topc @ X2)
% 0.41/0.62          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.41/0.62          | (m1_subset_1 @ (k1_tops_1 @ X2 @ X3) @ 
% 0.41/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X2))))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.62  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      ((![X17 : $i]:
% 0.41/0.62          (((X17) = (k1_xboole_0))
% 0.41/0.62           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62           | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.41/0.62           | ~ (r1_tarski @ X17 @ sk_B_1)))
% 0.41/0.62         <= ((![X17 : $i]:
% 0.41/0.62                (((X17) = (k1_xboole_0))
% 0.41/0.62                 | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r1_tarski @ X17 @ sk_B_1))))),
% 0.41/0.62      inference('split', [status(esa)], ['3'])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.41/0.62         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.41/0.62         | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 0.41/0.62         <= ((![X17 : $i]:
% 0.41/0.62                (((X17) = (k1_xboole_0))
% 0.41/0.62                 | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r1_tarski @ X17 @ sk_B_1))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      (((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.41/0.62         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)))
% 0.41/0.62         <= ((![X17 : $i]:
% 0.41/0.62                (((X17) = (k1_xboole_0))
% 0.41/0.62                 | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r1_tarski @ X17 @ sk_B_1))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['9', '16'])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(fc9_tops_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.41/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.62       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      (![X4 : $i, X5 : $i]:
% 0.41/0.62         (~ (l1_pre_topc @ X4)
% 0.41/0.62          | ~ (v2_pre_topc @ X4)
% 0.41/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.41/0.62          | (v3_pre_topc @ (k1_tops_1 @ X4 @ X5) @ X4))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.41/0.62        | ~ (v2_pre_topc @ sk_A)
% 0.41/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.62  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('23', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.41/0.62         <= ((![X17 : $i]:
% 0.41/0.62                (((X17) = (k1_xboole_0))
% 0.41/0.62                 | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r1_tarski @ X17 @ sk_B_1))))),
% 0.41/0.62      inference('demod', [status(thm)], ['17', '23'])).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t84_tops_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( l1_pre_topc @ A ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.62           ( ( v2_tops_1 @ B @ A ) <=>
% 0.41/0.62             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.62          | ((k1_tops_1 @ X16 @ X15) != (k1_xboole_0))
% 0.41/0.62          | (v2_tops_1 @ X15 @ X16)
% 0.41/0.62          | ~ (l1_pre_topc @ X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.41/0.62  thf('27', plain,
% 0.41/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.62        | (v2_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.62        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.41/0.62  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      (((v2_tops_1 @ sk_B_1 @ sk_A)
% 0.41/0.62        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B_1 @ sk_A)))
% 0.41/0.62         <= ((![X17 : $i]:
% 0.41/0.62                (((X17) = (k1_xboole_0))
% 0.41/0.62                 | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r1_tarski @ X17 @ sk_B_1))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['24', '29'])).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      (((v2_tops_1 @ sk_B_1 @ sk_A))
% 0.41/0.62         <= ((![X17 : $i]:
% 0.41/0.62                (((X17) = (k1_xboole_0))
% 0.41/0.62                 | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62                 | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r1_tarski @ X17 @ sk_B_1))))),
% 0.41/0.62      inference('simplify', [status(thm)], ['30'])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      (((r1_tarski @ sk_C @ sk_B_1) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      ((~ (v2_tops_1 @ sk_B_1 @ sk_A)) <= (~ ((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.41/0.62      inference('split', [status(esa)], ['32'])).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      (~
% 0.41/0.62       (![X17 : $i]:
% 0.41/0.62          (((X17) = (k1_xboole_0))
% 0.41/0.62           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62           | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.41/0.62           | ~ (r1_tarski @ X17 @ sk_B_1))) | 
% 0.41/0.62       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['31', '33'])).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.41/0.62       ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.62      inference('split', [status(esa)], ['1'])).
% 0.41/0.62  thf('36', plain,
% 0.41/0.62      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('sat_resolution*', [status(thm)], ['4', '34', '35'])).
% 0.41/0.62  thf('37', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('simpl_trail', [status(thm)], ['2', '36'])).
% 0.41/0.62  thf(t48_tops_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( l1_pre_topc @ A ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.62           ( ![C:$i]:
% 0.41/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.62               ( ( r1_tarski @ B @ C ) =>
% 0.41/0.62                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.41/0.62  thf('38', plain,
% 0.41/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.41/0.62          | ~ (r1_tarski @ X8 @ X10)
% 0.41/0.62          | (r1_tarski @ (k1_tops_1 @ X9 @ X8) @ (k1_tops_1 @ X9 @ X10))
% 0.41/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.41/0.62          | ~ (l1_pre_topc @ X9))),
% 0.41/0.62      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (l1_pre_topc @ sk_A)
% 0.41/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.41/0.62          | ~ (r1_tarski @ sk_C @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.41/0.62  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('41', plain,
% 0.41/0.62      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.41/0.62      inference('split', [status(esa)], ['41'])).
% 0.41/0.62  thf('43', plain,
% 0.41/0.62      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.41/0.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.41/0.62      inference('split', [status(esa)], ['1'])).
% 0.41/0.62  thf(t55_tops_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( l1_pre_topc @ B ) =>
% 0.41/0.62           ( ![C:$i]:
% 0.41/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.62               ( ![D:$i]:
% 0.41/0.62                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.62                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.41/0.62                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.41/0.62                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.41/0.62                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.62  thf('44', plain,
% 0.41/0.62      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.62         (~ (l1_pre_topc @ X11)
% 0.41/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.41/0.62          | ~ (v3_pre_topc @ X12 @ X11)
% 0.41/0.62          | ((k1_tops_1 @ X11 @ X12) = (X12))
% 0.41/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.41/0.62          | ~ (l1_pre_topc @ X14)
% 0.41/0.62          | ~ (v2_pre_topc @ X14))),
% 0.41/0.62      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.41/0.62  thf('45', plain,
% 0.41/0.62      ((![X11 : $i, X12 : $i]:
% 0.41/0.62          (~ (l1_pre_topc @ X11)
% 0.41/0.62           | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.41/0.62           | ~ (v3_pre_topc @ X12 @ X11)
% 0.41/0.62           | ((k1_tops_1 @ X11 @ X12) = (X12))))
% 0.41/0.62         <= ((![X11 : $i, X12 : $i]:
% 0.41/0.62                (~ (l1_pre_topc @ X11)
% 0.41/0.62                 | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.41/0.62                 | ~ (v3_pre_topc @ X12 @ X11)
% 0.41/0.62                 | ((k1_tops_1 @ X11 @ X12) = (X12)))))),
% 0.41/0.62      inference('split', [status(esa)], ['44'])).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('47', plain,
% 0.41/0.62      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.62         (~ (l1_pre_topc @ X11)
% 0.41/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.41/0.62          | ~ (v3_pre_topc @ X12 @ X11)
% 0.41/0.62          | ((k1_tops_1 @ X11 @ X12) = (X12))
% 0.41/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.41/0.62          | ~ (l1_pre_topc @ X14)
% 0.41/0.62          | ~ (v2_pre_topc @ X14))),
% 0.41/0.62      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      ((![X13 : $i, X14 : $i]:
% 0.41/0.62          (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.41/0.62           | ~ (l1_pre_topc @ X14)
% 0.41/0.62           | ~ (v2_pre_topc @ X14)))
% 0.41/0.62         <= ((![X13 : $i, X14 : $i]:
% 0.41/0.62                (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.41/0.62                 | ~ (l1_pre_topc @ X14)
% 0.41/0.62                 | ~ (v2_pre_topc @ X14))))),
% 0.41/0.62      inference('split', [status(esa)], ['47'])).
% 0.41/0.62  thf('49', plain,
% 0.41/0.62      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.41/0.62         <= ((![X13 : $i, X14 : $i]:
% 0.41/0.62                (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.41/0.62                 | ~ (l1_pre_topc @ X14)
% 0.41/0.62                 | ~ (v2_pre_topc @ X14))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['46', '48'])).
% 0.41/0.62  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      (~
% 0.41/0.62       (![X13 : $i, X14 : $i]:
% 0.41/0.62          (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.41/0.62           | ~ (l1_pre_topc @ X14)
% 0.41/0.62           | ~ (v2_pre_topc @ X14)))),
% 0.41/0.62      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.41/0.62  thf('53', plain,
% 0.41/0.62      ((![X11 : $i, X12 : $i]:
% 0.41/0.62          (~ (l1_pre_topc @ X11)
% 0.41/0.62           | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.41/0.62           | ~ (v3_pre_topc @ X12 @ X11)
% 0.41/0.62           | ((k1_tops_1 @ X11 @ X12) = (X12)))) | 
% 0.41/0.62       (![X13 : $i, X14 : $i]:
% 0.41/0.62          (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.41/0.62           | ~ (l1_pre_topc @ X14)
% 0.41/0.62           | ~ (v2_pre_topc @ X14)))),
% 0.41/0.62      inference('split', [status(esa)], ['47'])).
% 0.41/0.62  thf('54', plain,
% 0.41/0.62      ((![X11 : $i, X12 : $i]:
% 0.41/0.62          (~ (l1_pre_topc @ X11)
% 0.41/0.62           | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.41/0.62           | ~ (v3_pre_topc @ X12 @ X11)
% 0.41/0.62           | ((k1_tops_1 @ X11 @ X12) = (X12))))),
% 0.41/0.62      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.41/0.62  thf('55', plain,
% 0.41/0.62      (![X11 : $i, X12 : $i]:
% 0.41/0.62         (~ (l1_pre_topc @ X11)
% 0.41/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.41/0.62          | ~ (v3_pre_topc @ X12 @ X11)
% 0.41/0.62          | ((k1_tops_1 @ X11 @ X12) = (X12)))),
% 0.41/0.62      inference('simpl_trail', [status(thm)], ['45', '54'])).
% 0.41/0.62  thf('56', plain,
% 0.41/0.62      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))
% 0.41/0.62         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.41/0.62         | ~ (l1_pre_topc @ sk_A)))
% 0.41/0.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['43', '55'])).
% 0.41/0.62  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('58', plain,
% 0.41/0.62      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.41/0.62         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.41/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.41/0.62  thf('59', plain,
% 0.41/0.62      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.41/0.62         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.41/0.62             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['42', '58'])).
% 0.41/0.62  thf('60', plain,
% 0.41/0.62      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.62      inference('split', [status(esa)], ['41'])).
% 0.41/0.62  thf('61', plain, (((v3_pre_topc @ sk_C @ sk_A))),
% 0.41/0.62      inference('sat_resolution*', [status(thm)], ['4', '34', '60'])).
% 0.41/0.62  thf('62', plain,
% 0.41/0.62      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('sat_resolution*', [status(thm)], ['4', '34', '35'])).
% 0.41/0.62  thf('63', plain, (((k1_tops_1 @ sk_A @ sk_C) = (sk_C))),
% 0.41/0.62      inference('simpl_trail', [status(thm)], ['59', '61', '62'])).
% 0.41/0.62  thf('64', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62          | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.41/0.62          | ~ (r1_tarski @ sk_C @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['39', '40', '63'])).
% 0.41/0.62  thf('65', plain,
% 0.41/0.62      ((~ (r1_tarski @ sk_C @ sk_B_1)
% 0.41/0.62        | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['0', '64'])).
% 0.41/0.62  thf('66', plain,
% 0.41/0.62      (((r1_tarski @ sk_C @ sk_B_1)) <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.41/0.62      inference('split', [status(esa)], ['32'])).
% 0.41/0.62  thf('67', plain,
% 0.41/0.62      (((r1_tarski @ sk_C @ sk_B_1)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.62      inference('split', [status(esa)], ['32'])).
% 0.41/0.62  thf('68', plain, (((r1_tarski @ sk_C @ sk_B_1))),
% 0.41/0.62      inference('sat_resolution*', [status(thm)], ['4', '34', '67'])).
% 0.41/0.62  thf('69', plain, ((r1_tarski @ sk_C @ sk_B_1)),
% 0.41/0.62      inference('simpl_trail', [status(thm)], ['66', '68'])).
% 0.41/0.62  thf('70', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('71', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.62          | ~ (v2_tops_1 @ X15 @ X16)
% 0.41/0.62          | ((k1_tops_1 @ X16 @ X15) = (k1_xboole_0))
% 0.41/0.62          | ~ (l1_pre_topc @ X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.41/0.62  thf('72', plain,
% 0.41/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.62        | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.41/0.62        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['70', '71'])).
% 0.41/0.62  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('74', plain,
% 0.41/0.62      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.41/0.62        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['72', '73'])).
% 0.41/0.62  thf('75', plain,
% 0.41/0.62      (((v2_tops_1 @ sk_B_1 @ sk_A)) <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.41/0.62      inference('split', [status(esa)], ['3'])).
% 0.41/0.62  thf('76', plain, (((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.62      inference('sat_resolution*', [status(thm)], ['4', '34'])).
% 0.41/0.62  thf('77', plain, ((v2_tops_1 @ sk_B_1 @ sk_A)),
% 0.41/0.62      inference('simpl_trail', [status(thm)], ['75', '76'])).
% 0.41/0.62  thf('78', plain, (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['74', '77'])).
% 0.41/0.62  thf('79', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.41/0.62      inference('demod', [status(thm)], ['65', '69', '78'])).
% 0.41/0.62  thf(t3_xboole_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.62  thf('80', plain,
% 0.41/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.41/0.62  thf('81', plain, (((sk_C) = (k1_xboole_0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['79', '80'])).
% 0.41/0.62  thf('82', plain,
% 0.41/0.62      ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('83', plain,
% 0.41/0.62      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.41/0.62      inference('split', [status(esa)], ['82'])).
% 0.41/0.62  thf('84', plain,
% 0.41/0.62      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.41/0.62      inference('split', [status(esa)], ['82'])).
% 0.41/0.62  thf('85', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.41/0.62      inference('sat_resolution*', [status(thm)], ['4', '34', '84'])).
% 0.41/0.62  thf('86', plain, (((sk_C) != (k1_xboole_0))),
% 0.41/0.62      inference('simpl_trail', [status(thm)], ['83', '85'])).
% 0.41/0.62  thf('87', plain, ($false),
% 0.41/0.62      inference('simplify_reflect-', [status(thm)], ['81', '86'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
