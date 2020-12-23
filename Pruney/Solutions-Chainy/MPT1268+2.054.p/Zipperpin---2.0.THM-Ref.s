%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.alUYPjQWyx

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:23 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 272 expanded)
%              Number of leaves         :   25 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          :  998 (3790 expanded)
%              Number of equality atoms :   38 ( 135 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X23 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X23 @ sk_A )
      | ~ ( r1_tarski @ X23 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('20',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('24',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k1_tops_1 @ X22 @ X21 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ~ ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('40',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('41',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tops_1 @ X21 @ X22 )
      | ( ( k1_tops_1 @ X22 @ X21 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('49',plain,
    ( ( r1_tarski @ k1_xboole_0 @ sk_B )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ k1_xboole_0 @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('56',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('59',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('60',plain,
    ( ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('61',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('62',plain,
    ( ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('66',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('67',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

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

thf('73',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','76'])).

thf('78',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_C @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','77'])).

thf('79',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('80',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','80'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('82',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ( sk_C = k1_xboole_0 ) )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ sk_C @ k1_xboole_0 ) )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','83'])).

thf('85',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','80'])).

thf('86',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','38','39','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.alUYPjQWyx
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:25:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 586 iterations in 0.096s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.56  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.56  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.56  thf(t86_tops_1, conjecture,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( ( v2_tops_1 @ B @ A ) <=>
% 0.36/0.56             ( ![C:$i]:
% 0.36/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.36/0.56                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i]:
% 0.36/0.56        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.56          ( ![B:$i]:
% 0.36/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56              ( ( v2_tops_1 @ B @ A ) <=>
% 0.36/0.56                ( ![C:$i]:
% 0.36/0.56                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.36/0.56                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.36/0.56  thf('0', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.56      inference('split', [status(esa)], ['2'])).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      (![X23 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56          | ((X23) = (k1_xboole_0))
% 0.36/0.56          | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.36/0.56          | ~ (r1_tarski @ X23 @ sk_B)
% 0.36/0.56          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      ((![X23 : $i]:
% 0.36/0.56          (((X23) = (k1_xboole_0))
% 0.36/0.56           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.36/0.56           | ~ (r1_tarski @ X23 @ sk_B))) | 
% 0.36/0.56       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.56      inference('split', [status(esa)], ['4'])).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t3_subset, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      (![X11 : $i, X12 : $i]:
% 0.36/0.56         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.56  thf('8', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t44_tops_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_pre_topc @ A ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      (![X16 : $i, X17 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.56          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.36/0.56          | ~ (l1_pre_topc @ X17))),
% 0.36/0.56      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.56  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('13', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.36/0.56      inference('demod', [status(thm)], ['11', '12'])).
% 0.36/0.56  thf(t1_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.56       ( r1_tarski @ A @ C ) ))).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X3 @ X4)
% 0.36/0.56          | ~ (r1_tarski @ X4 @ X5)
% 0.36/0.56          | (r1_tarski @ X3 @ X5))),
% 0.36/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.56  thf('15', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.36/0.56          | ~ (r1_tarski @ sk_B @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['8', '15'])).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      (![X11 : $i, X13 : $i]:
% 0.36/0.56         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      ((![X23 : $i]:
% 0.36/0.56          (((X23) = (k1_xboole_0))
% 0.36/0.56           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.36/0.56           | ~ (r1_tarski @ X23 @ sk_B)))
% 0.36/0.56         <= ((![X23 : $i]:
% 0.36/0.56                (((X23) = (k1_xboole_0))
% 0.36/0.56                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.36/0.56                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.36/0.56      inference('split', [status(esa)], ['4'])).
% 0.36/0.56  thf('20', plain,
% 0.36/0.56      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.36/0.56         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.36/0.56         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.36/0.56         <= ((![X23 : $i]:
% 0.36/0.56                (((X23) = (k1_xboole_0))
% 0.36/0.56                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.36/0.56                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.56  thf('21', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.36/0.56      inference('demod', [status(thm)], ['11', '12'])).
% 0.36/0.56  thf('22', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(fc9_tops_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.36/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.56       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      (![X14 : $i, X15 : $i]:
% 0.36/0.56         (~ (l1_pre_topc @ X14)
% 0.36/0.56          | ~ (v2_pre_topc @ X14)
% 0.36/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.36/0.56          | (v3_pre_topc @ (k1_tops_1 @ X14 @ X15) @ X14))),
% 0.36/0.56      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.36/0.56  thf('24', plain,
% 0.36/0.56      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.36/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.56  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('27', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.36/0.56      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.36/0.56         <= ((![X23 : $i]:
% 0.36/0.56                (((X23) = (k1_xboole_0))
% 0.36/0.56                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.36/0.56                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.36/0.56      inference('demod', [status(thm)], ['20', '21', '27'])).
% 0.36/0.56  thf('29', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t84_tops_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_pre_topc @ A ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( ( v2_tops_1 @ B @ A ) <=>
% 0.36/0.56             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.36/0.56  thf('30', plain,
% 0.36/0.56      (![X21 : $i, X22 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.36/0.56          | ((k1_tops_1 @ X22 @ X21) != (k1_xboole_0))
% 0.36/0.56          | (v2_tops_1 @ X21 @ X22)
% 0.36/0.56          | ~ (l1_pre_topc @ X22))),
% 0.36/0.56      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.56        | (v2_tops_1 @ sk_B @ sk_A)
% 0.36/0.56        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.56  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('33', plain,
% 0.36/0.56      (((v2_tops_1 @ sk_B @ sk_A)
% 0.36/0.56        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.36/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.36/0.56  thf('34', plain,
% 0.36/0.56      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.36/0.56         <= ((![X23 : $i]:
% 0.36/0.56                (((X23) = (k1_xboole_0))
% 0.36/0.56                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.36/0.56                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['28', '33'])).
% 0.36/0.56  thf('35', plain,
% 0.36/0.56      (((v2_tops_1 @ sk_B @ sk_A))
% 0.36/0.56         <= ((![X23 : $i]:
% 0.36/0.56                (((X23) = (k1_xboole_0))
% 0.36/0.56                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.36/0.56                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.36/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.36/0.56  thf('36', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.56      inference('split', [status(esa)], ['36'])).
% 0.36/0.56  thf('38', plain,
% 0.36/0.56      (~
% 0.36/0.56       (![X23 : $i]:
% 0.36/0.56          (((X23) = (k1_xboole_0))
% 0.36/0.56           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.36/0.56           | ~ (r1_tarski @ X23 @ sk_B))) | 
% 0.36/0.56       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['35', '37'])).
% 0.36/0.56  thf('39', plain,
% 0.36/0.56      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.56      inference('split', [status(esa)], ['36'])).
% 0.36/0.56  thf('40', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.56  thf('41', plain,
% 0.36/0.56      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.56      inference('split', [status(esa)], ['4'])).
% 0.36/0.56  thf('42', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('43', plain,
% 0.36/0.56      (![X21 : $i, X22 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.36/0.56          | ~ (v2_tops_1 @ X21 @ X22)
% 0.36/0.56          | ((k1_tops_1 @ X22 @ X21) = (k1_xboole_0))
% 0.36/0.56          | ~ (l1_pre_topc @ X22))),
% 0.36/0.56      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.36/0.56  thf('44', plain,
% 0.36/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.56        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.36/0.56        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.56  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('46', plain,
% 0.36/0.56      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.36/0.56        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.56  thf('47', plain,
% 0.36/0.56      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.36/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['41', '46'])).
% 0.36/0.56  thf('48', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.36/0.56      inference('demod', [status(thm)], ['11', '12'])).
% 0.36/0.56  thf('49', plain,
% 0.36/0.56      (((r1_tarski @ k1_xboole_0 @ sk_B)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['47', '48'])).
% 0.36/0.56  thf('50', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X3 @ X4)
% 0.36/0.56          | ~ (r1_tarski @ X4 @ X5)
% 0.36/0.56          | (r1_tarski @ X3 @ X5))),
% 0.36/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.56  thf('51', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          ((r1_tarski @ k1_xboole_0 @ X0) | ~ (r1_tarski @ sk_B @ X0)))
% 0.36/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.56  thf('52', plain,
% 0.36/0.56      (((r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['40', '51'])).
% 0.36/0.56  thf('53', plain,
% 0.36/0.56      (![X11 : $i, X13 : $i]:
% 0.36/0.56         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.56  thf('54', plain,
% 0.36/0.56      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.36/0.56  thf('55', plain,
% 0.36/0.56      (![X16 : $i, X17 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.56          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.36/0.56          | ~ (l1_pre_topc @ X17))),
% 0.36/0.56      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.36/0.56  thf('56', plain,
% 0.36/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.36/0.56         | (r1_tarski @ (k1_tops_1 @ sk_A @ k1_xboole_0) @ k1_xboole_0)))
% 0.36/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.56  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('58', plain,
% 0.36/0.56      (((r1_tarski @ (k1_tops_1 @ sk_A @ k1_xboole_0) @ k1_xboole_0))
% 0.36/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.36/0.56  thf(l32_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.56  thf('59', plain,
% 0.36/0.56      (![X0 : $i, X2 : $i]:
% 0.36/0.56         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.56  thf('60', plain,
% 0.36/0.56      ((((k4_xboole_0 @ (k1_tops_1 @ sk_A @ k1_xboole_0) @ k1_xboole_0)
% 0.36/0.56          = (k1_xboole_0)))
% 0.36/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.36/0.56  thf(t79_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.36/0.56  thf('61', plain,
% 0.36/0.56      (![X9 : $i, X10 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X10)),
% 0.36/0.56      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.36/0.56  thf('62', plain,
% 0.36/0.56      (((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.36/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['60', '61'])).
% 0.36/0.56  thf('63', plain,
% 0.36/0.56      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.36/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['41', '46'])).
% 0.36/0.56  thf('64', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('65', plain,
% 0.36/0.56      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.36/0.56      inference('split', [status(esa)], ['2'])).
% 0.36/0.56  thf('66', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.56  thf('67', plain,
% 0.36/0.56      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.36/0.56      inference('split', [status(esa)], ['36'])).
% 0.36/0.56  thf('68', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X3 @ X4)
% 0.36/0.56          | ~ (r1_tarski @ X4 @ X5)
% 0.36/0.56          | (r1_tarski @ X3 @ X5))),
% 0.36/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.56  thf('69', plain,
% 0.36/0.56      ((![X0 : $i]: ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ sk_B @ X0)))
% 0.36/0.56         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.36/0.56  thf('70', plain,
% 0.36/0.56      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.36/0.56         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['66', '69'])).
% 0.36/0.56  thf('71', plain,
% 0.36/0.56      (![X11 : $i, X13 : $i]:
% 0.36/0.56         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.56  thf('72', plain,
% 0.36/0.56      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.56         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['70', '71'])).
% 0.36/0.56  thf(t56_tops_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( l1_pre_topc @ A ) =>
% 0.36/0.56       ( ![B:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56           ( ![C:$i]:
% 0.36/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.56               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.56                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf('73', plain,
% 0.36/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.56         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.36/0.56          | ~ (v3_pre_topc @ X18 @ X19)
% 0.36/0.56          | ~ (r1_tarski @ X18 @ X20)
% 0.36/0.56          | (r1_tarski @ X18 @ (k1_tops_1 @ X19 @ X20))
% 0.36/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.36/0.56          | ~ (l1_pre_topc @ X19))),
% 0.36/0.56      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.36/0.56  thf('74', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (l1_pre_topc @ sk_A)
% 0.36/0.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.36/0.56           | ~ (r1_tarski @ sk_C @ X0)
% 0.36/0.56           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.36/0.56         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['72', '73'])).
% 0.36/0.56  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('76', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.56           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.36/0.56           | ~ (r1_tarski @ sk_C @ X0)
% 0.36/0.56           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.36/0.56         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.36/0.56      inference('demod', [status(thm)], ['74', '75'])).
% 0.36/0.56  thf('77', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (r1_tarski @ sk_C @ X0)
% 0.36/0.56           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.36/0.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.36/0.56         <= (((r1_tarski @ sk_C @ sk_B)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['65', '76'])).
% 0.36/0.56  thf('78', plain,
% 0.36/0.56      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))
% 0.36/0.56         | ~ (r1_tarski @ sk_C @ sk_B)))
% 0.36/0.56         <= (((r1_tarski @ sk_C @ sk_B)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['64', '77'])).
% 0.36/0.56  thf('79', plain,
% 0.36/0.56      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.36/0.56      inference('split', [status(esa)], ['36'])).
% 0.36/0.56  thf('80', plain,
% 0.36/0.56      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.56         <= (((r1_tarski @ sk_C @ sk_B)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['78', '79'])).
% 0.36/0.56  thf('81', plain,
% 0.36/0.56      (((r1_tarski @ sk_C @ k1_xboole_0))
% 0.36/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.36/0.56             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.36/0.56             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['63', '80'])).
% 0.36/0.56  thf(t67_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.36/0.56         ( r1_xboole_0 @ B @ C ) ) =>
% 0.36/0.56       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.56  thf('82', plain,
% 0.36/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.56         (((X6) = (k1_xboole_0))
% 0.36/0.56          | ~ (r1_tarski @ X6 @ X7)
% 0.36/0.56          | ~ (r1_tarski @ X6 @ X8)
% 0.36/0.56          | ~ (r1_xboole_0 @ X7 @ X8))),
% 0.36/0.56      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.36/0.56  thf('83', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.56           | ~ (r1_tarski @ sk_C @ X0)
% 0.36/0.56           | ((sk_C) = (k1_xboole_0))))
% 0.36/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.36/0.56             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.36/0.56             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['81', '82'])).
% 0.36/0.56  thf('84', plain,
% 0.36/0.56      (((((sk_C) = (k1_xboole_0)) | ~ (r1_tarski @ sk_C @ k1_xboole_0)))
% 0.36/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.36/0.56             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.36/0.56             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['62', '83'])).
% 0.36/0.56  thf('85', plain,
% 0.36/0.56      (((r1_tarski @ sk_C @ k1_xboole_0))
% 0.36/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.36/0.56             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.36/0.56             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['63', '80'])).
% 0.36/0.56  thf('86', plain,
% 0.36/0.56      ((((sk_C) = (k1_xboole_0)))
% 0.36/0.56         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.36/0.56             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.36/0.56             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['84', '85'])).
% 0.36/0.56  thf('87', plain,
% 0.36/0.56      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('88', plain,
% 0.36/0.56      ((((sk_C) != (sk_C)))
% 0.36/0.56         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.36/0.56             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.36/0.56             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.36/0.56             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['86', '87'])).
% 0.36/0.56  thf('89', plain,
% 0.36/0.56      (~ ((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.36/0.56       ~ ((v3_pre_topc @ sk_C @ sk_A)) | (((sk_C) = (k1_xboole_0)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['88'])).
% 0.36/0.56  thf('90', plain, ($false),
% 0.36/0.56      inference('sat_resolution*', [status(thm)],
% 0.36/0.56                ['1', '3', '5', '38', '39', '89'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
