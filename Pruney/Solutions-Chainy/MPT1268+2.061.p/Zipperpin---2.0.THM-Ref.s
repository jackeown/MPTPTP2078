%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.poBfgdshp6

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 850 expanded)
%              Number of leaves         :   22 ( 227 expanded)
%              Depth                    :   20
%              Number of atoms          : 1251 (13159 expanded)
%              Number of equality atoms :   60 ( 545 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

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

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ( r1_tarski @ ( k1_tops_1 @ X12 @ X11 ) @ ( k1_tops_1 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('4',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
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

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X14 )
      | ( ( k1_tops_1 @ X14 @ X15 )
        = X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('11',plain,
    ( ! [X14: $i,X15: $i] :
        ( ~ ( l1_pre_topc @ X14 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
        | ~ ( v3_pre_topc @ X15 @ X14 )
        | ( ( k1_tops_1 @ X14 @ X15 )
          = X15 ) )
   <= ! [X14: $i,X15: $i] :
        ( ~ ( l1_pre_topc @ X14 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
        | ~ ( v3_pre_topc @ X15 @ X14 )
        | ( ( k1_tops_1 @ X14 @ X15 )
          = X15 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X14 )
      | ( ( k1_tops_1 @ X14 @ X15 )
        = X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('14',plain,
    ( ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( l1_pre_topc @ X17 )
        | ~ ( v2_pre_topc @ X17 ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( l1_pre_topc @ X17 )
        | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( l1_pre_topc @ X17 )
        | ~ ( v2_pre_topc @ X17 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ~ ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( l1_pre_topc @ X17 )
        | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ! [X14: $i,X15: $i] :
        ( ~ ( l1_pre_topc @ X14 )
        | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
        | ~ ( v3_pre_topc @ X15 @ X14 )
        | ( ( k1_tops_1 @ X14 @ X15 )
          = X15 ) )
    | ! [X16: $i,X17: $i] :
        ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( l1_pre_topc @ X17 )
        | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X14 )
      | ( ( k1_tops_1 @ X14 @ X15 )
        = X15 ) ) ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X14 )
      | ( ( k1_tops_1 @ X14 @ X15 )
        = X15 ) ) ),
    inference(simpl_trail,[status(thm)],['11','20'])).

thf('22',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C )
        = sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C )
        = sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X10 @ X9 ) @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['35','36'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X20: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X20 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X20 @ sk_A )
      | ~ ( r1_tarski @ X20 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['35','36'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X7 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('49',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','52'])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k1_tops_1 @ X19 @ X18 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('62',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ! [X20: $i] :
          ( ( X20 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X20 @ sk_A )
          | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('64',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('65',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference(split,[status(esa)],['43'])).

thf('72',plain,
    ( ( ~ ( r1_tarski @ sk_C @ sk_B )
      | ~ ( v3_pre_topc @ sk_C @ sk_A )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ! [X20: $i] :
          ( ( X20 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X20 @ sk_A )
          | ~ ( r1_tarski @ X20 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('74',plain,
    ( ( ~ ( v3_pre_topc @ sk_C @ sk_A )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ! [X20: $i] :
          ( ( X20 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X20 @ sk_A )
          | ~ ( r1_tarski @ X20 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ! [X20: $i] :
          ( ( X20 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X20 @ sk_A )
          | ~ ( r1_tarski @ X20 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','74'])).

thf('76',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('77',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ! [X20: $i] :
          ( ( X20 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X20 @ sk_A )
          | ~ ( r1_tarski @ X20 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ! [X20: $i] :
          ( ( X20 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X20 @ sk_A )
          | ~ ( r1_tarski @ X20 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference(split,[status(esa)],['43'])).

thf('80',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('81',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['27','29','62','78','79','80'])).

thf('82',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['27','80','29','62','78','79','82'])).

thf('84',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['25','81','83'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['27','80','29','62','78','79','82'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','87'])).

thf('89',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('90',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference('sat_resolution*',[status(thm)],['80','29','62','78','79','27'])).

thf('91',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(simpl_trail,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['43'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tops_1 @ X18 @ X19 )
      | ( ( k1_tops_1 @ X19 @ X18 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['27','80','29','62','78','79'])).

thf('100',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['98','99'])).

thf('101',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['88','91','100'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('102',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('103',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('105',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['27','80','62','78','79','29'])).

thf('106',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['103','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.poBfgdshp6
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 241 iterations in 0.066s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.20/0.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(t86_tops_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.50             ( ![C:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.20/0.50                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50              ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.50                ( ![C:$i]:
% 0.20/0.50                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.20/0.50                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.50         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf(t48_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50               ( ( r1_tarski @ B @ C ) =>
% 0.20/0.50                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.50          | ~ (r1_tarski @ X11 @ X13)
% 0.20/0.50          | (r1_tarski @ (k1_tops_1 @ X12 @ X11) @ (k1_tops_1 @ X12 @ X13))
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.50          | ~ (l1_pre_topc @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (l1_pre_topc @ sk_A)
% 0.20/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.50           | ~ (r1_tarski @ sk_C @ X0)))
% 0.20/0.50         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.50           | ~ (r1_tarski @ sk_C @ X0)))
% 0.20/0.50         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.50         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf(t55_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_pre_topc @ B ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.50                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.20/0.50                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.20/0.50                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.20/0.50                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.50          | ~ (v3_pre_topc @ X15 @ X14)
% 0.20/0.50          | ((k1_tops_1 @ X14 @ X15) = (X15))
% 0.20/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.50          | ~ (l1_pre_topc @ X17)
% 0.20/0.50          | ~ (v2_pre_topc @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((![X14 : $i, X15 : $i]:
% 0.20/0.50          (~ (l1_pre_topc @ X14)
% 0.20/0.50           | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.50           | ~ (v3_pre_topc @ X15 @ X14)
% 0.20/0.50           | ((k1_tops_1 @ X14 @ X15) = (X15))))
% 0.20/0.50         <= ((![X14 : $i, X15 : $i]:
% 0.20/0.50                (~ (l1_pre_topc @ X14)
% 0.20/0.50                 | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X15 @ X14)
% 0.20/0.50                 | ((k1_tops_1 @ X14 @ X15) = (X15)))))),
% 0.20/0.50      inference('split', [status(esa)], ['10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.50          | ~ (v3_pre_topc @ X15 @ X14)
% 0.20/0.50          | ((k1_tops_1 @ X14 @ X15) = (X15))
% 0.20/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.50          | ~ (l1_pre_topc @ X17)
% 0.20/0.50          | ~ (v2_pre_topc @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((![X16 : $i, X17 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.50           | ~ (l1_pre_topc @ X17)
% 0.20/0.50           | ~ (v2_pre_topc @ X17)))
% 0.20/0.50         <= ((![X16 : $i, X17 : $i]:
% 0.20/0.50                (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.50                 | ~ (l1_pre_topc @ X17)
% 0.20/0.50                 | ~ (v2_pre_topc @ X17))))),
% 0.20/0.50      inference('split', [status(esa)], ['13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.20/0.50         <= ((![X16 : $i, X17 : $i]:
% 0.20/0.50                (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.50                 | ~ (l1_pre_topc @ X17)
% 0.20/0.50                 | ~ (v2_pre_topc @ X17))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.50  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (~
% 0.20/0.50       (![X16 : $i, X17 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.50           | ~ (l1_pre_topc @ X17)
% 0.20/0.50           | ~ (v2_pre_topc @ X17)))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((![X14 : $i, X15 : $i]:
% 0.20/0.50          (~ (l1_pre_topc @ X14)
% 0.20/0.50           | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.50           | ~ (v3_pre_topc @ X15 @ X14)
% 0.20/0.50           | ((k1_tops_1 @ X14 @ X15) = (X15)))) | 
% 0.20/0.50       (![X16 : $i, X17 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.50           | ~ (l1_pre_topc @ X17)
% 0.20/0.50           | ~ (v2_pre_topc @ X17)))),
% 0.20/0.50      inference('split', [status(esa)], ['13'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((![X14 : $i, X15 : $i]:
% 0.20/0.50          (~ (l1_pre_topc @ X14)
% 0.20/0.50           | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.50           | ~ (v3_pre_topc @ X15 @ X14)
% 0.20/0.50           | ((k1_tops_1 @ X14 @ X15) = (X15))))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.50          | ~ (v3_pre_topc @ X15 @ X14)
% 0.20/0.50          | ((k1_tops_1 @ X14 @ X15) = (X15)))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['11', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))
% 0.20/0.50         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.20/0.50         | ~ (l1_pre_topc @ sk_A)))
% 0.20/0.50         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '21'])).
% 0.20/0.50  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.20/0.50         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.20/0.50         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.20/0.50             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '24'])).
% 0.20/0.50  thf('26', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['26'])).
% 0.20/0.50  thf('28', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t3_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.50  thf('32', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t44_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.50          | (r1_tarski @ (k1_tops_1 @ X10 @ X9) @ X9)
% 0.20/0.50          | ~ (l1_pre_topc @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf(t1_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.50       ( r1_tarski @ A @ C ) ))).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.50          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.50          | (r1_tarski @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.20/0.50          | ~ (r1_tarski @ sk_B @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X4 : $i, X6 : $i]:
% 0.20/0.50         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X20 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ((X20) = (k1_xboole_0))
% 0.20/0.50          | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50          | ~ (r1_tarski @ X20 @ sk_B)
% 0.20/0.50          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      ((![X20 : $i]:
% 0.20/0.50          (((X20) = (k1_xboole_0))
% 0.20/0.50           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50           | ~ (r1_tarski @ X20 @ sk_B)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                (((X20) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.50         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.50         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                (((X20) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['42', '44'])).
% 0.20/0.50  thf('46', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(fc9_tops_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X7)
% 0.20/0.50          | ~ (v2_pre_topc @ X7)
% 0.20/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.50          | (v3_pre_topc @ (k1_tops_1 @ X7 @ X8) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('52', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                (((X20) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['45', '46', '52'])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t84_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.50             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.50          | ((k1_tops_1 @ X19 @ X18) != (k1_xboole_0))
% 0.20/0.50          | (v2_tops_1 @ X18 @ X19)
% 0.20/0.50          | ~ (l1_pre_topc @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v2_tops_1 @ sk_B @ sk_A)
% 0.20/0.50        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.50  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A)
% 0.20/0.50        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                (((X20) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '58'])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                (((X20) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['26'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.20/0.50       ~
% 0.20/0.50       (![X20 : $i]:
% 0.20/0.50          (((X20) = (k1_xboole_0))
% 0.20/0.50           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50           | ~ (r1_tarski @ X20 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['7'])).
% 0.20/0.50  thf('64', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['26'])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.50          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.50          | (r1_tarski @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      ((![X0 : $i]: ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ sk_B @ X0)))
% 0.20/0.50         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.20/0.50         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['64', '67'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (![X4 : $i, X6 : $i]:
% 0.20/0.50         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.50         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      ((![X20 : $i]:
% 0.20/0.50          (((X20) = (k1_xboole_0))
% 0.20/0.50           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50           | ~ (r1_tarski @ X20 @ sk_B)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                (((X20) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['43'])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      (((~ (r1_tarski @ sk_C @ sk_B)
% 0.20/0.50         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.20/0.50         | ((sk_C) = (k1_xboole_0))))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                (((X20) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X20 @ sk_B))) & 
% 0.20/0.50             ((r1_tarski @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['26'])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      (((~ (v3_pre_topc @ sk_C @ sk_A) | ((sk_C) = (k1_xboole_0))))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                (((X20) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X20 @ sk_B))) & 
% 0.20/0.50             ((r1_tarski @ sk_C @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['72', '73'])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      ((((sk_C) = (k1_xboole_0)))
% 0.20/0.50         <= ((![X20 : $i]:
% 0.20/0.50                (((X20) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X20 @ sk_B))) & 
% 0.20/0.50             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.50             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['63', '74'])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['28'])).
% 0.20/0.50  thf('77', plain,
% 0.20/0.50      ((((sk_C) != (sk_C)))
% 0.20/0.50         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.20/0.50             (![X20 : $i]:
% 0.20/0.50                (((X20) = (k1_xboole_0))
% 0.20/0.50                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50                 | ~ (r1_tarski @ X20 @ sk_B))) & 
% 0.20/0.50             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.20/0.50             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      (~
% 0.20/0.50       (![X20 : $i]:
% 0.20/0.50          (((X20) = (k1_xboole_0))
% 0.20/0.50           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50           | ~ (r1_tarski @ X20 @ sk_B))) | 
% 0.20/0.50       ~ ((v3_pre_topc @ sk_C @ sk_A)) | (((sk_C) = (k1_xboole_0))) | 
% 0.20/0.50       ~ ((r1_tarski @ sk_C @ sk_B))),
% 0.20/0.50      inference('simplify', [status(thm)], ['77'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.20/0.50       (![X20 : $i]:
% 0.20/0.50          (((X20) = (k1_xboole_0))
% 0.20/0.50           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.20/0.50           | ~ (r1_tarski @ X20 @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['43'])).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['7'])).
% 0.20/0.50  thf('81', plain, (((v3_pre_topc @ sk_C @ sk_A))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)],
% 0.20/0.50                ['27', '29', '62', '78', '79', '80'])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.50       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf('83', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)],
% 0.20/0.50                ['27', '80', '29', '62', '78', '79', '82'])).
% 0.20/0.50  thf('84', plain, (((k1_tops_1 @ sk_A @ sk_C) = (sk_C))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['25', '81', '83'])).
% 0.20/0.50  thf('85', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.50           | ~ (r1_tarski @ sk_C @ X0)))
% 0.20/0.50         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '84'])).
% 0.20/0.50  thf('86', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)],
% 0.20/0.50                ['27', '80', '29', '62', '78', '79', '82'])).
% 0.20/0.50  thf('87', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.50          | ~ (r1_tarski @ sk_C @ X0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.20/0.50  thf('88', plain,
% 0.20/0.50      ((~ (r1_tarski @ sk_C @ sk_B)
% 0.20/0.50        | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '87'])).
% 0.20/0.50  thf('89', plain,
% 0.20/0.50      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['26'])).
% 0.20/0.50  thf('90', plain, (((r1_tarski @ sk_C @ sk_B))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)],
% 0.20/0.50                ['80', '29', '62', '78', '79', '27'])).
% 0.20/0.50  thf('91', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['89', '90'])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['43'])).
% 0.20/0.50  thf('93', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('94', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.50          | ~ (v2_tops_1 @ X18 @ X19)
% 0.20/0.50          | ((k1_tops_1 @ X19 @ X18) = (k1_xboole_0))
% 0.20/0.50          | ~ (l1_pre_topc @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.20/0.50  thf('95', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.50  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('97', plain,
% 0.20/0.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['95', '96'])).
% 0.20/0.50  thf('98', plain,
% 0.20/0.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.50         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['92', '97'])).
% 0.20/0.50  thf('99', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)],
% 0.20/0.50                ['27', '80', '29', '62', '78', '79'])).
% 0.20/0.50  thf('100', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['98', '99'])).
% 0.20/0.50  thf('101', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.20/0.50      inference('demod', [status(thm)], ['88', '91', '100'])).
% 0.20/0.50  thf(t3_xboole_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('102', plain,
% 0.20/0.50      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.50  thf('103', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.50  thf('104', plain,
% 0.20/0.50      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['28'])).
% 0.20/0.50  thf('105', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)],
% 0.20/0.50                ['27', '80', '62', '78', '79', '29'])).
% 0.20/0.50  thf('106', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['104', '105'])).
% 0.20/0.50  thf('107', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['103', '106'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
