%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RA2hkmg6u0

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:19 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 173 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  859 (2327 expanded)
%              Number of equality atoms :   37 (  92 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
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

thf('40',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tops_1 @ X21 @ X22 )
      | ( ( k1_tops_1 @ X22 @ X21 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('49',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('50',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('51',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

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

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','59'])).

thf('61',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_C @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','60'])).

thf('62',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('63',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','63'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('67',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('69',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','72'])).

thf('74',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','38','39','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RA2hkmg6u0
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:14:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.20/1.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.20/1.41  % Solved by: fo/fo7.sh
% 1.20/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.41  % done 2117 iterations in 0.963s
% 1.20/1.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.20/1.41  % SZS output start Refutation
% 1.20/1.41  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.20/1.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.20/1.41  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.20/1.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.20/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.41  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.41  thf(sk_C_type, type, sk_C: $i).
% 1.20/1.41  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.20/1.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.20/1.41  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.20/1.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.20/1.41  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.20/1.41  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.20/1.41  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 1.20/1.41  thf(t86_tops_1, conjecture,
% 1.20/1.41    (![A:$i]:
% 1.20/1.41     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.20/1.41       ( ![B:$i]:
% 1.20/1.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.41           ( ( v2_tops_1 @ B @ A ) <=>
% 1.20/1.41             ( ![C:$i]:
% 1.20/1.41               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.41                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 1.20/1.41                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 1.20/1.41  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.41    (~( ![A:$i]:
% 1.20/1.41        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.20/1.41          ( ![B:$i]:
% 1.20/1.41            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.41              ( ( v2_tops_1 @ B @ A ) <=>
% 1.20/1.41                ( ![C:$i]:
% 1.20/1.41                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.41                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 1.20/1.41                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 1.20/1.41    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 1.20/1.41  thf('0', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('1', plain,
% 1.20/1.41      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.20/1.41      inference('split', [status(esa)], ['0'])).
% 1.20/1.41  thf('2', plain,
% 1.20/1.41      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('3', plain,
% 1.20/1.41      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.20/1.41      inference('split', [status(esa)], ['2'])).
% 1.20/1.41  thf('4', plain,
% 1.20/1.41      (![X23 : $i]:
% 1.20/1.41         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.41          | ((X23) = (k1_xboole_0))
% 1.20/1.41          | ~ (v3_pre_topc @ X23 @ sk_A)
% 1.20/1.41          | ~ (r1_tarski @ X23 @ sk_B)
% 1.20/1.41          | (v2_tops_1 @ sk_B @ sk_A))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('5', plain,
% 1.20/1.41      ((![X23 : $i]:
% 1.20/1.41          (((X23) = (k1_xboole_0))
% 1.20/1.41           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.41           | ~ (v3_pre_topc @ X23 @ sk_A)
% 1.20/1.41           | ~ (r1_tarski @ X23 @ sk_B))) | 
% 1.20/1.41       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.20/1.41      inference('split', [status(esa)], ['4'])).
% 1.20/1.41  thf('6', plain,
% 1.20/1.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf(t3_subset, axiom,
% 1.20/1.41    (![A:$i,B:$i]:
% 1.20/1.41     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.20/1.41  thf('7', plain,
% 1.20/1.41      (![X11 : $i, X12 : $i]:
% 1.20/1.41         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.20/1.41      inference('cnf', [status(esa)], [t3_subset])).
% 1.20/1.41  thf('8', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.20/1.41      inference('sup-', [status(thm)], ['6', '7'])).
% 1.20/1.41  thf('9', plain,
% 1.20/1.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf(t44_tops_1, axiom,
% 1.20/1.41    (![A:$i]:
% 1.20/1.41     ( ( l1_pre_topc @ A ) =>
% 1.20/1.41       ( ![B:$i]:
% 1.20/1.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.41           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.20/1.41  thf('10', plain,
% 1.20/1.41      (![X16 : $i, X17 : $i]:
% 1.20/1.41         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.20/1.41          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 1.20/1.41          | ~ (l1_pre_topc @ X17))),
% 1.20/1.41      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.20/1.41  thf('11', plain,
% 1.20/1.41      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.20/1.41      inference('sup-', [status(thm)], ['9', '10'])).
% 1.20/1.41  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('13', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.20/1.41      inference('demod', [status(thm)], ['11', '12'])).
% 1.20/1.41  thf(t1_xboole_1, axiom,
% 1.20/1.41    (![A:$i,B:$i,C:$i]:
% 1.20/1.41     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.20/1.41       ( r1_tarski @ A @ C ) ))).
% 1.20/1.41  thf('14', plain,
% 1.20/1.41      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.20/1.41         (~ (r1_tarski @ X6 @ X7)
% 1.20/1.41          | ~ (r1_tarski @ X7 @ X8)
% 1.20/1.41          | (r1_tarski @ X6 @ X8))),
% 1.20/1.41      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.20/1.41  thf('15', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.20/1.41          | ~ (r1_tarski @ sk_B @ X0))),
% 1.20/1.41      inference('sup-', [status(thm)], ['13', '14'])).
% 1.20/1.41  thf('16', plain,
% 1.20/1.41      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.20/1.41      inference('sup-', [status(thm)], ['8', '15'])).
% 1.20/1.41  thf('17', plain,
% 1.20/1.41      (![X11 : $i, X13 : $i]:
% 1.20/1.41         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 1.20/1.41      inference('cnf', [status(esa)], [t3_subset])).
% 1.20/1.41  thf('18', plain,
% 1.20/1.41      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.20/1.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['16', '17'])).
% 1.20/1.41  thf('19', plain,
% 1.20/1.41      ((![X23 : $i]:
% 1.20/1.41          (((X23) = (k1_xboole_0))
% 1.20/1.41           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.41           | ~ (v3_pre_topc @ X23 @ sk_A)
% 1.20/1.41           | ~ (r1_tarski @ X23 @ sk_B)))
% 1.20/1.41         <= ((![X23 : $i]:
% 1.20/1.41                (((X23) = (k1_xboole_0))
% 1.20/1.41                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.41                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 1.20/1.41                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 1.20/1.41      inference('split', [status(esa)], ['4'])).
% 1.20/1.41  thf('20', plain,
% 1.20/1.41      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.20/1.42         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.20/1.42         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 1.20/1.42         <= ((![X23 : $i]:
% 1.20/1.42                (((X23) = (k1_xboole_0))
% 1.20/1.42                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.42                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 1.20/1.42                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 1.20/1.42      inference('sup-', [status(thm)], ['18', '19'])).
% 1.20/1.42  thf('21', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.20/1.42      inference('demod', [status(thm)], ['11', '12'])).
% 1.20/1.42  thf('22', plain,
% 1.20/1.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf(fc9_tops_1, axiom,
% 1.20/1.42    (![A:$i,B:$i]:
% 1.20/1.42     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.20/1.42         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.20/1.42       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.20/1.42  thf('23', plain,
% 1.20/1.42      (![X14 : $i, X15 : $i]:
% 1.20/1.42         (~ (l1_pre_topc @ X14)
% 1.20/1.42          | ~ (v2_pre_topc @ X14)
% 1.20/1.42          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.20/1.42          | (v3_pre_topc @ (k1_tops_1 @ X14 @ X15) @ X14))),
% 1.20/1.42      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.20/1.42  thf('24', plain,
% 1.20/1.42      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.20/1.42        | ~ (v2_pre_topc @ sk_A)
% 1.20/1.42        | ~ (l1_pre_topc @ sk_A))),
% 1.20/1.42      inference('sup-', [status(thm)], ['22', '23'])).
% 1.20/1.42  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('27', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.20/1.42      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.20/1.42  thf('28', plain,
% 1.20/1.42      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.20/1.42         <= ((![X23 : $i]:
% 1.20/1.42                (((X23) = (k1_xboole_0))
% 1.20/1.42                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.42                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 1.20/1.42                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 1.20/1.42      inference('demod', [status(thm)], ['20', '21', '27'])).
% 1.20/1.42  thf('29', plain,
% 1.20/1.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf(t84_tops_1, axiom,
% 1.20/1.42    (![A:$i]:
% 1.20/1.42     ( ( l1_pre_topc @ A ) =>
% 1.20/1.42       ( ![B:$i]:
% 1.20/1.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.42           ( ( v2_tops_1 @ B @ A ) <=>
% 1.20/1.42             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.20/1.42  thf('30', plain,
% 1.20/1.42      (![X21 : $i, X22 : $i]:
% 1.20/1.42         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.20/1.42          | ((k1_tops_1 @ X22 @ X21) != (k1_xboole_0))
% 1.20/1.42          | (v2_tops_1 @ X21 @ X22)
% 1.20/1.42          | ~ (l1_pre_topc @ X22))),
% 1.20/1.42      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.20/1.42  thf('31', plain,
% 1.20/1.42      ((~ (l1_pre_topc @ sk_A)
% 1.20/1.42        | (v2_tops_1 @ sk_B @ sk_A)
% 1.20/1.42        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['29', '30'])).
% 1.20/1.42  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('33', plain,
% 1.20/1.42      (((v2_tops_1 @ sk_B @ sk_A)
% 1.20/1.42        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 1.20/1.42      inference('demod', [status(thm)], ['31', '32'])).
% 1.20/1.42  thf('34', plain,
% 1.20/1.42      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 1.20/1.42         <= ((![X23 : $i]:
% 1.20/1.42                (((X23) = (k1_xboole_0))
% 1.20/1.42                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.42                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 1.20/1.42                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 1.20/1.42      inference('sup-', [status(thm)], ['28', '33'])).
% 1.20/1.42  thf('35', plain,
% 1.20/1.42      (((v2_tops_1 @ sk_B @ sk_A))
% 1.20/1.42         <= ((![X23 : $i]:
% 1.20/1.42                (((X23) = (k1_xboole_0))
% 1.20/1.42                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.42                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 1.20/1.42                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 1.20/1.42      inference('simplify', [status(thm)], ['34'])).
% 1.20/1.42  thf('36', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('37', plain,
% 1.20/1.42      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 1.20/1.42      inference('split', [status(esa)], ['36'])).
% 1.20/1.42  thf('38', plain,
% 1.20/1.42      (~
% 1.20/1.42       (![X23 : $i]:
% 1.20/1.42          (((X23) = (k1_xboole_0))
% 1.20/1.42           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.42           | ~ (v3_pre_topc @ X23 @ sk_A)
% 1.20/1.42           | ~ (r1_tarski @ X23 @ sk_B))) | 
% 1.20/1.42       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.20/1.42      inference('sup-', [status(thm)], ['35', '37'])).
% 1.20/1.42  thf('39', plain,
% 1.20/1.42      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.20/1.42      inference('split', [status(esa)], ['36'])).
% 1.20/1.42  thf('40', plain,
% 1.20/1.42      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.20/1.42      inference('split', [status(esa)], ['4'])).
% 1.20/1.42  thf('41', plain,
% 1.20/1.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('42', plain,
% 1.20/1.42      (![X21 : $i, X22 : $i]:
% 1.20/1.42         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.20/1.42          | ~ (v2_tops_1 @ X21 @ X22)
% 1.20/1.42          | ((k1_tops_1 @ X22 @ X21) = (k1_xboole_0))
% 1.20/1.42          | ~ (l1_pre_topc @ X22))),
% 1.20/1.42      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.20/1.42  thf('43', plain,
% 1.20/1.42      ((~ (l1_pre_topc @ sk_A)
% 1.20/1.42        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.20/1.42        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.20/1.42      inference('sup-', [status(thm)], ['41', '42'])).
% 1.20/1.42  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('45', plain,
% 1.20/1.42      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.20/1.42        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.20/1.42      inference('demod', [status(thm)], ['43', '44'])).
% 1.20/1.42  thf('46', plain,
% 1.20/1.42      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.20/1.42         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['40', '45'])).
% 1.20/1.42  thf('47', plain,
% 1.20/1.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('48', plain,
% 1.20/1.42      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 1.20/1.42      inference('split', [status(esa)], ['2'])).
% 1.20/1.42  thf('49', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.20/1.42      inference('sup-', [status(thm)], ['6', '7'])).
% 1.20/1.42  thf('50', plain,
% 1.20/1.42      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 1.20/1.42      inference('split', [status(esa)], ['36'])).
% 1.20/1.42  thf('51', plain,
% 1.20/1.42      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.20/1.42         (~ (r1_tarski @ X6 @ X7)
% 1.20/1.42          | ~ (r1_tarski @ X7 @ X8)
% 1.20/1.42          | (r1_tarski @ X6 @ X8))),
% 1.20/1.42      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.20/1.42  thf('52', plain,
% 1.20/1.42      ((![X0 : $i]: ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ sk_B @ X0)))
% 1.20/1.42         <= (((r1_tarski @ sk_C @ sk_B)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['50', '51'])).
% 1.20/1.42  thf('53', plain,
% 1.20/1.42      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))
% 1.20/1.42         <= (((r1_tarski @ sk_C @ sk_B)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['49', '52'])).
% 1.20/1.42  thf('54', plain,
% 1.20/1.42      (![X11 : $i, X13 : $i]:
% 1.20/1.42         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 1.20/1.42      inference('cnf', [status(esa)], [t3_subset])).
% 1.20/1.42  thf('55', plain,
% 1.20/1.42      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.20/1.42         <= (((r1_tarski @ sk_C @ sk_B)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['53', '54'])).
% 1.20/1.42  thf(t56_tops_1, axiom,
% 1.20/1.42    (![A:$i]:
% 1.20/1.42     ( ( l1_pre_topc @ A ) =>
% 1.20/1.42       ( ![B:$i]:
% 1.20/1.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.42           ( ![C:$i]:
% 1.20/1.42             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.42               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.20/1.42                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.20/1.42  thf('56', plain,
% 1.20/1.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.20/1.42         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.20/1.42          | ~ (v3_pre_topc @ X18 @ X19)
% 1.20/1.42          | ~ (r1_tarski @ X18 @ X20)
% 1.20/1.42          | (r1_tarski @ X18 @ (k1_tops_1 @ X19 @ X20))
% 1.20/1.42          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.20/1.42          | ~ (l1_pre_topc @ X19))),
% 1.20/1.42      inference('cnf', [status(esa)], [t56_tops_1])).
% 1.20/1.42  thf('57', plain,
% 1.20/1.42      ((![X0 : $i]:
% 1.20/1.42          (~ (l1_pre_topc @ sk_A)
% 1.20/1.42           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.42           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 1.20/1.42           | ~ (r1_tarski @ sk_C @ X0)
% 1.20/1.42           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 1.20/1.42         <= (((r1_tarski @ sk_C @ sk_B)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['55', '56'])).
% 1.20/1.42  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('59', plain,
% 1.20/1.42      ((![X0 : $i]:
% 1.20/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.42           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 1.20/1.42           | ~ (r1_tarski @ sk_C @ X0)
% 1.20/1.42           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 1.20/1.42         <= (((r1_tarski @ sk_C @ sk_B)))),
% 1.20/1.42      inference('demod', [status(thm)], ['57', '58'])).
% 1.20/1.42  thf('60', plain,
% 1.20/1.42      ((![X0 : $i]:
% 1.20/1.42          (~ (r1_tarski @ sk_C @ X0)
% 1.20/1.42           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 1.20/1.42           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.20/1.42         <= (((r1_tarski @ sk_C @ sk_B)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['48', '59'])).
% 1.20/1.42  thf('61', plain,
% 1.20/1.42      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))
% 1.20/1.42         | ~ (r1_tarski @ sk_C @ sk_B)))
% 1.20/1.42         <= (((r1_tarski @ sk_C @ sk_B)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['47', '60'])).
% 1.20/1.42  thf('62', plain,
% 1.20/1.42      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 1.20/1.42      inference('split', [status(esa)], ['36'])).
% 1.20/1.42  thf('63', plain,
% 1.20/1.42      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.20/1.42         <= (((r1_tarski @ sk_C @ sk_B)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 1.20/1.42      inference('demod', [status(thm)], ['61', '62'])).
% 1.20/1.42  thf('64', plain,
% 1.20/1.42      (((r1_tarski @ sk_C @ k1_xboole_0))
% 1.20/1.42         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 1.20/1.42             ((r1_tarski @ sk_C @ sk_B)) & 
% 1.20/1.42             ((v3_pre_topc @ sk_C @ sk_A)))),
% 1.20/1.42      inference('sup+', [status(thm)], ['46', '63'])).
% 1.20/1.42  thf(d10_xboole_0, axiom,
% 1.20/1.42    (![A:$i,B:$i]:
% 1.20/1.42     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.20/1.42  thf('65', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.20/1.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.42  thf('66', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.20/1.42      inference('simplify', [status(thm)], ['65'])).
% 1.20/1.42  thf(l32_xboole_1, axiom,
% 1.20/1.42    (![A:$i,B:$i]:
% 1.20/1.42     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.20/1.42  thf('67', plain,
% 1.20/1.42      (![X3 : $i, X5 : $i]:
% 1.20/1.42         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 1.20/1.42      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.20/1.42  thf('68', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.20/1.42      inference('sup-', [status(thm)], ['66', '67'])).
% 1.20/1.42  thf(t36_xboole_1, axiom,
% 1.20/1.42    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.20/1.42  thf('69', plain,
% 1.20/1.42      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 1.20/1.42      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.20/1.42  thf('70', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.20/1.42      inference('sup+', [status(thm)], ['68', '69'])).
% 1.20/1.42  thf('71', plain,
% 1.20/1.42      (![X0 : $i, X2 : $i]:
% 1.20/1.42         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.20/1.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.42  thf('72', plain,
% 1.20/1.42      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['70', '71'])).
% 1.20/1.42  thf('73', plain,
% 1.20/1.42      ((((sk_C) = (k1_xboole_0)))
% 1.20/1.42         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 1.20/1.42             ((r1_tarski @ sk_C @ sk_B)) & 
% 1.20/1.42             ((v3_pre_topc @ sk_C @ sk_A)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['64', '72'])).
% 1.20/1.42  thf('74', plain,
% 1.20/1.42      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.20/1.42      inference('split', [status(esa)], ['0'])).
% 1.20/1.42  thf('75', plain,
% 1.20/1.42      ((((sk_C) != (sk_C)))
% 1.20/1.42         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 1.20/1.42             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 1.20/1.42             ((r1_tarski @ sk_C @ sk_B)) & 
% 1.20/1.42             ((v3_pre_topc @ sk_C @ sk_A)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['73', '74'])).
% 1.20/1.42  thf('76', plain,
% 1.20/1.42      (~ ((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 1.20/1.42       ~ ((v3_pre_topc @ sk_C @ sk_A)) | (((sk_C) = (k1_xboole_0)))),
% 1.20/1.42      inference('simplify', [status(thm)], ['75'])).
% 1.20/1.42  thf('77', plain, ($false),
% 1.20/1.42      inference('sat_resolution*', [status(thm)],
% 1.20/1.42                ['1', '3', '5', '38', '39', '76'])).
% 1.20/1.42  
% 1.20/1.42  % SZS output end Refutation
% 1.20/1.42  
% 1.20/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
