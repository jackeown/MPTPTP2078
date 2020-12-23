%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p8IAV2TDY3

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 491 expanded)
%              Number of leaves         :   22 ( 135 expanded)
%              Depth                    :   19
%              Number of atoms          : 1002 (7960 expanded)
%              Number of equality atoms :   46 ( 330 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    ! [X19: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X19 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X19 @ sk_A )
      | ~ ( r1_tarski @ X19 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X9 @ X8 ) @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) )
   <= ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('16',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X6 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('19',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','22'])).

thf('24',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k1_tops_1 @ X18 @ X17 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X19: $i] :
        ( ( X19 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X19 @ sk_A )
        | ~ ( r1_tarski @ X19 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ~ ! [X19: $i] :
          ( ( X19 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X19 @ sk_A )
          | ~ ( r1_tarski @ X19 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ( r1_tarski @ ( k1_tops_1 @ X11 @ X10 ) @ ( k1_tops_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( ( k1_tops_1 @ X13 @ X14 )
        = X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('45',plain,
    ( ! [X13: $i,X14: $i] :
        ( ~ ( l1_pre_topc @ X13 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
        | ~ ( v3_pre_topc @ X14 @ X13 )
        | ( ( k1_tops_1 @ X13 @ X14 )
          = X14 ) )
   <= ! [X13: $i,X14: $i] :
        ( ~ ( l1_pre_topc @ X13 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
        | ~ ( v3_pre_topc @ X14 @ X13 )
        | ( ( k1_tops_1 @ X13 @ X14 )
          = X14 ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( ( k1_tops_1 @ X13 @ X14 )
        = X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('48',plain,
    ( ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) )
   <= ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ! [X13: $i,X14: $i] :
        ( ~ ( l1_pre_topc @ X13 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
        | ~ ( v3_pre_topc @ X14 @ X13 )
        | ( ( k1_tops_1 @ X13 @ X14 )
          = X14 ) )
    | ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(split,[status(esa)],['47'])).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( ( k1_tops_1 @ X13 @ X14 )
        = X14 ) ) ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( ( k1_tops_1 @ X13 @ X14 )
        = X14 ) ) ),
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
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
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
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','64'])).

thf('66',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['32'])).

thf('67',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('68',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference('sat_resolution*',[status(thm)],['4','34','67'])).

thf('69',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(simpl_trail,[status(thm)],['66','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tops_1 @ X17 @ X18 )
      | ( ( k1_tops_1 @ X18 @ X17 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('75',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','34'])).

thf('76',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73','76'])).

thf('78',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['65','69','77'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('79',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
    | ( k1_xboole_0 = sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('81',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('82',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['83'])).

thf('86',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','34','85'])).

thf('87',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['84','86'])).

thf('88',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['82','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p8IAV2TDY3
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:37:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 156 iterations in 0.051s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.22/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(t86_tops_1, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48           ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.48             ( ![C:$i]:
% 0.22/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.22/0.48                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48              ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.48                ( ![C:$i]:
% 0.22/0.48                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.22/0.48                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.48         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.48      inference('split', [status(esa)], ['1'])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X19 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | ((X19) = (k1_xboole_0))
% 0.22/0.48          | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.22/0.48          | ~ (r1_tarski @ X19 @ sk_B)
% 0.22/0.48          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.22/0.48       (![X19 : $i]:
% 0.22/0.48          (((X19) = (k1_xboole_0))
% 0.22/0.48           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48           | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.22/0.48           | ~ (r1_tarski @ X19 @ sk_B)))),
% 0.22/0.48      inference('split', [status(esa)], ['3'])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t44_tops_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.48          | (r1_tarski @ (k1_tops_1 @ X9 @ X8) @ X8)
% 0.22/0.48          | ~ (l1_pre_topc @ X9))),
% 0.22/0.48      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.48  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('9', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.22/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_k1_tops_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( l1_pre_topc @ A ) & 
% 0.22/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.48       ( m1_subset_1 @
% 0.22/0.48         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X4 : $i, X5 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X4)
% 0.22/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.22/0.48          | (m1_subset_1 @ (k1_tops_1 @ X4 @ X5) @ 
% 0.22/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.22/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.22/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      ((![X19 : $i]:
% 0.22/0.48          (((X19) = (k1_xboole_0))
% 0.22/0.48           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48           | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.22/0.48           | ~ (r1_tarski @ X19 @ sk_B)))
% 0.22/0.48         <= ((![X19 : $i]:
% 0.22/0.48                (((X19) = (k1_xboole_0))
% 0.22/0.48                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48                 | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.22/0.48                 | ~ (r1_tarski @ X19 @ sk_B))))),
% 0.22/0.48      inference('split', [status(esa)], ['3'])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.22/0.48         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.48         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.22/0.48         <= ((![X19 : $i]:
% 0.22/0.48                (((X19) = (k1_xboole_0))
% 0.22/0.48                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48                 | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.22/0.48                 | ~ (r1_tarski @ X19 @ sk_B))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(fc9_tops_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.22/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.48       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X6 : $i, X7 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X6)
% 0.22/0.48          | ~ (v2_pre_topc @ X6)
% 0.22/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.22/0.48          | (v3_pre_topc @ (k1_tops_1 @ X6 @ X7) @ X6))),
% 0.22/0.48      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.48        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.48  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('22', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.48      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.22/0.48         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.22/0.48         <= ((![X19 : $i]:
% 0.22/0.48                (((X19) = (k1_xboole_0))
% 0.22/0.48                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48                 | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.22/0.48                 | ~ (r1_tarski @ X19 @ sk_B))))),
% 0.22/0.48      inference('demod', [status(thm)], ['16', '22'])).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.22/0.48         <= ((![X19 : $i]:
% 0.22/0.48                (((X19) = (k1_xboole_0))
% 0.22/0.48                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48                 | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.22/0.48                 | ~ (r1_tarski @ X19 @ sk_B))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '23'])).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t84_tops_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48           ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.48             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      (![X17 : $i, X18 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.48          | ((k1_tops_1 @ X18 @ X17) != (k1_xboole_0))
% 0.22/0.48          | (v2_tops_1 @ X17 @ X18)
% 0.22/0.48          | ~ (l1_pre_topc @ X18))),
% 0.22/0.48      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.22/0.48  thf('27', plain,
% 0.22/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.48        | (v2_tops_1 @ sk_B @ sk_A)
% 0.22/0.48        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.48  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('29', plain,
% 0.22/0.48      (((v2_tops_1 @ sk_B @ sk_A)
% 0.22/0.48        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.22/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.48  thf('30', plain,
% 0.22/0.48      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.22/0.48         <= ((![X19 : $i]:
% 0.22/0.48                (((X19) = (k1_xboole_0))
% 0.22/0.48                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48                 | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.22/0.48                 | ~ (r1_tarski @ X19 @ sk_B))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['24', '29'])).
% 0.22/0.48  thf('31', plain,
% 0.22/0.48      (((v2_tops_1 @ sk_B @ sk_A))
% 0.22/0.48         <= ((![X19 : $i]:
% 0.22/0.48                (((X19) = (k1_xboole_0))
% 0.22/0.48                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48                 | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.22/0.48                 | ~ (r1_tarski @ X19 @ sk_B))))),
% 0.22/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.48  thf('32', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('33', plain,
% 0.22/0.48      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.48      inference('split', [status(esa)], ['32'])).
% 0.22/0.48  thf('34', plain,
% 0.22/0.48      (~
% 0.22/0.48       (![X19 : $i]:
% 0.22/0.48          (((X19) = (k1_xboole_0))
% 0.22/0.48           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48           | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.22/0.48           | ~ (r1_tarski @ X19 @ sk_B))) | 
% 0.22/0.48       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['31', '33'])).
% 0.22/0.48  thf('35', plain,
% 0.22/0.48      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.22/0.48       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('split', [status(esa)], ['1'])).
% 0.22/0.48  thf('36', plain,
% 0.22/0.48      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['4', '34', '35'])).
% 0.22/0.48  thf('37', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('simpl_trail', [status(thm)], ['2', '36'])).
% 0.22/0.48  thf(t48_tops_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48               ( ( r1_tarski @ B @ C ) =>
% 0.22/0.48                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf('38', plain,
% 0.22/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.48          | ~ (r1_tarski @ X10 @ X12)
% 0.22/0.48          | (r1_tarski @ (k1_tops_1 @ X11 @ X10) @ (k1_tops_1 @ X11 @ X12))
% 0.22/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.48          | ~ (l1_pre_topc @ X11))),
% 0.22/0.48      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.22/0.48  thf('39', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ sk_A)
% 0.22/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.22/0.48          | ~ (r1_tarski @ sk_C @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.48  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('41', plain,
% 0.22/0.48      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('42', plain,
% 0.22/0.48      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.22/0.48      inference('split', [status(esa)], ['41'])).
% 0.22/0.48  thf('43', plain,
% 0.22/0.48      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.48         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.48      inference('split', [status(esa)], ['1'])).
% 0.22/0.48  thf(t55_tops_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( l1_pre_topc @ B ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48               ( ![D:$i]:
% 0.22/0.48                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.48                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.22/0.48                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.22/0.48                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.22/0.48                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf('44', plain,
% 0.22/0.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X13)
% 0.22/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.48          | ~ (v3_pre_topc @ X14 @ X13)
% 0.22/0.48          | ((k1_tops_1 @ X13 @ X14) = (X14))
% 0.22/0.48          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.48          | ~ (l1_pre_topc @ X16)
% 0.22/0.48          | ~ (v2_pre_topc @ X16))),
% 0.22/0.48      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.22/0.48  thf('45', plain,
% 0.22/0.48      ((![X13 : $i, X14 : $i]:
% 0.22/0.48          (~ (l1_pre_topc @ X13)
% 0.22/0.48           | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.48           | ~ (v3_pre_topc @ X14 @ X13)
% 0.22/0.48           | ((k1_tops_1 @ X13 @ X14) = (X14))))
% 0.22/0.48         <= ((![X13 : $i, X14 : $i]:
% 0.22/0.48                (~ (l1_pre_topc @ X13)
% 0.22/0.48                 | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.48                 | ~ (v3_pre_topc @ X14 @ X13)
% 0.22/0.48                 | ((k1_tops_1 @ X13 @ X14) = (X14)))))),
% 0.22/0.48      inference('split', [status(esa)], ['44'])).
% 0.22/0.48  thf('46', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('47', plain,
% 0.22/0.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X13)
% 0.22/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.48          | ~ (v3_pre_topc @ X14 @ X13)
% 0.22/0.48          | ((k1_tops_1 @ X13 @ X14) = (X14))
% 0.22/0.48          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.48          | ~ (l1_pre_topc @ X16)
% 0.22/0.48          | ~ (v2_pre_topc @ X16))),
% 0.22/0.48      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.22/0.48  thf('48', plain,
% 0.22/0.48      ((![X15 : $i, X16 : $i]:
% 0.22/0.48          (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.48           | ~ (l1_pre_topc @ X16)
% 0.22/0.48           | ~ (v2_pre_topc @ X16)))
% 0.22/0.48         <= ((![X15 : $i, X16 : $i]:
% 0.22/0.48                (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.48                 | ~ (l1_pre_topc @ X16)
% 0.22/0.48                 | ~ (v2_pre_topc @ X16))))),
% 0.22/0.48      inference('split', [status(esa)], ['47'])).
% 0.22/0.48  thf('49', plain,
% 0.22/0.48      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.22/0.48         <= ((![X15 : $i, X16 : $i]:
% 0.22/0.48                (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.48                 | ~ (l1_pre_topc @ X16)
% 0.22/0.48                 | ~ (v2_pre_topc @ X16))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['46', '48'])).
% 0.22/0.48  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('52', plain,
% 0.22/0.48      (~
% 0.22/0.48       (![X15 : $i, X16 : $i]:
% 0.22/0.48          (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.48           | ~ (l1_pre_topc @ X16)
% 0.22/0.48           | ~ (v2_pre_topc @ X16)))),
% 0.22/0.48      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.22/0.48  thf('53', plain,
% 0.22/0.48      ((![X13 : $i, X14 : $i]:
% 0.22/0.48          (~ (l1_pre_topc @ X13)
% 0.22/0.48           | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.48           | ~ (v3_pre_topc @ X14 @ X13)
% 0.22/0.48           | ((k1_tops_1 @ X13 @ X14) = (X14)))) | 
% 0.22/0.48       (![X15 : $i, X16 : $i]:
% 0.22/0.48          (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.48           | ~ (l1_pre_topc @ X16)
% 0.22/0.48           | ~ (v2_pre_topc @ X16)))),
% 0.22/0.48      inference('split', [status(esa)], ['47'])).
% 0.22/0.48  thf('54', plain,
% 0.22/0.48      ((![X13 : $i, X14 : $i]:
% 0.22/0.48          (~ (l1_pre_topc @ X13)
% 0.22/0.48           | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.48           | ~ (v3_pre_topc @ X14 @ X13)
% 0.22/0.48           | ((k1_tops_1 @ X13 @ X14) = (X14))))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.22/0.48  thf('55', plain,
% 0.22/0.48      (![X13 : $i, X14 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X13)
% 0.22/0.48          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.48          | ~ (v3_pre_topc @ X14 @ X13)
% 0.22/0.48          | ((k1_tops_1 @ X13 @ X14) = (X14)))),
% 0.22/0.48      inference('simpl_trail', [status(thm)], ['45', '54'])).
% 0.22/0.48  thf('56', plain,
% 0.22/0.48      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))
% 0.22/0.48         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.22/0.48         | ~ (l1_pre_topc @ sk_A)))
% 0.22/0.48         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['43', '55'])).
% 0.22/0.48  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('58', plain,
% 0.22/0.48      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.22/0.48         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.48      inference('demod', [status(thm)], ['56', '57'])).
% 0.22/0.48  thf('59', plain,
% 0.22/0.48      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.22/0.48         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.22/0.48             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['42', '58'])).
% 0.22/0.48  thf('60', plain,
% 0.22/0.48      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('split', [status(esa)], ['41'])).
% 0.22/0.48  thf('61', plain, (((v3_pre_topc @ sk_C @ sk_A))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['4', '34', '60'])).
% 0.22/0.48  thf('62', plain,
% 0.22/0.48      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['4', '34', '35'])).
% 0.22/0.48  thf('63', plain, (((k1_tops_1 @ sk_A @ sk_C) = (sk_C))),
% 0.22/0.48      inference('simpl_trail', [status(thm)], ['59', '61', '62'])).
% 0.22/0.48  thf('64', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48          | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.22/0.48          | ~ (r1_tarski @ sk_C @ X0))),
% 0.22/0.48      inference('demod', [status(thm)], ['39', '40', '63'])).
% 0.22/0.48  thf('65', plain,
% 0.22/0.48      ((~ (r1_tarski @ sk_C @ sk_B)
% 0.22/0.48        | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '64'])).
% 0.22/0.48  thf('66', plain,
% 0.22/0.48      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.22/0.48      inference('split', [status(esa)], ['32'])).
% 0.22/0.48  thf('67', plain,
% 0.22/0.48      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('split', [status(esa)], ['32'])).
% 0.22/0.48  thf('68', plain, (((r1_tarski @ sk_C @ sk_B))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['4', '34', '67'])).
% 0.22/0.48  thf('69', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.22/0.48      inference('simpl_trail', [status(thm)], ['66', '68'])).
% 0.22/0.48  thf('70', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('71', plain,
% 0.22/0.48      (![X17 : $i, X18 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.48          | ~ (v2_tops_1 @ X17 @ X18)
% 0.22/0.48          | ((k1_tops_1 @ X18 @ X17) = (k1_xboole_0))
% 0.22/0.48          | ~ (l1_pre_topc @ X18))),
% 0.22/0.48      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.22/0.48  thf('72', plain,
% 0.22/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.48        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.48        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.48  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('74', plain,
% 0.22/0.48      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.48      inference('split', [status(esa)], ['3'])).
% 0.22/0.48  thf('75', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['4', '34'])).
% 0.22/0.48  thf('76', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.22/0.48      inference('simpl_trail', [status(thm)], ['74', '75'])).
% 0.22/0.48  thf('77', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['72', '73', '76'])).
% 0.22/0.48  thf('78', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.22/0.48      inference('demod', [status(thm)], ['65', '69', '77'])).
% 0.22/0.48  thf(d10_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.48  thf('79', plain,
% 0.22/0.48      (![X0 : $i, X2 : $i]:
% 0.22/0.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.48  thf('80', plain,
% 0.22/0.48      ((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['78', '79'])).
% 0.22/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.48  thf('81', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.48  thf('82', plain, (((k1_xboole_0) = (sk_C))),
% 0.22/0.48      inference('demod', [status(thm)], ['80', '81'])).
% 0.22/0.48  thf('83', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('84', plain,
% 0.22/0.48      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.22/0.48      inference('split', [status(esa)], ['83'])).
% 0.22/0.48  thf('85', plain,
% 0.22/0.48      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('split', [status(esa)], ['83'])).
% 0.22/0.48  thf('86', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['4', '34', '85'])).
% 0.22/0.48  thf('87', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.48      inference('simpl_trail', [status(thm)], ['84', '86'])).
% 0.22/0.48  thf('88', plain, ($false),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['82', '87'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
