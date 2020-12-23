%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p3f6BoXDWO

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:17 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 172 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  848 (2314 expanded)
%              Number of equality atoms :   35 (  89 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X20: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X20 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X20 @ sk_A )
      | ~ ( r1_tarski @ X20 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) )
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
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X14 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
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
    inference(split,[status(esa)],['4'])).

thf('20',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X11 @ X12 ) @ X11 ) ) ),
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
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k1_tops_1 @ X19 @ X18 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,
    ( ~ ! [X20: $i] :
          ( ( X20 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X20 @ sk_A )
          | ~ ( r1_tarski @ X20 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tops_1 @ X18 @ X19 )
      | ( ( k1_tops_1 @ X19 @ X18 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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
    inference(split,[status(esa)],['38'])).

thf('49',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('50',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
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
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
    inference(split,[status(esa)],['2'])).

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

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('65',plain,(
    ! [X6: $i] :
      ( ( k1_subset_1 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('66',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf('67',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_subset_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_C @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','37','39','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p3f6BoXDWO
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.86  % Solved by: fo/fo7.sh
% 0.61/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.86  % done 1581 iterations in 0.419s
% 0.61/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.86  % SZS output start Refutation
% 0.61/0.86  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.61/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.61/0.86  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.61/0.86  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.61/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.86  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.61/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.61/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.86  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.61/0.86  thf(t86_tops_1, conjecture,
% 0.61/0.86    (![A:$i]:
% 0.61/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.86       ( ![B:$i]:
% 0.61/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.86           ( ( v2_tops_1 @ B @ A ) <=>
% 0.61/0.86             ( ![C:$i]:
% 0.61/0.86               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.86                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.61/0.86                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.61/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.86    (~( ![A:$i]:
% 0.61/0.86        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.61/0.86          ( ![B:$i]:
% 0.61/0.86            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.86              ( ( v2_tops_1 @ B @ A ) <=>
% 0.61/0.86                ( ![C:$i]:
% 0.61/0.86                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.86                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.61/0.86                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.61/0.86    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.61/0.86  thf('0', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('1', plain,
% 0.61/0.86      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.86      inference('split', [status(esa)], ['0'])).
% 0.61/0.86  thf('2', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('3', plain,
% 0.61/0.86      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.86      inference('split', [status(esa)], ['2'])).
% 0.61/0.86  thf('4', plain,
% 0.61/0.86      (![X20 : $i]:
% 0.61/0.86         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.86          | ((X20) = (k1_xboole_0))
% 0.61/0.86          | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.61/0.86          | ~ (r1_tarski @ X20 @ sk_B)
% 0.61/0.86          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('5', plain,
% 0.61/0.86      ((![X20 : $i]:
% 0.61/0.86          (((X20) = (k1_xboole_0))
% 0.61/0.86           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.86           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.61/0.86           | ~ (r1_tarski @ X20 @ sk_B))) | 
% 0.61/0.86       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.86      inference('split', [status(esa)], ['4'])).
% 0.61/0.86  thf('6', plain,
% 0.61/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf(t3_subset, axiom,
% 0.61/0.86    (![A:$i,B:$i]:
% 0.61/0.86     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.61/0.86  thf('7', plain,
% 0.61/0.86      (![X8 : $i, X9 : $i]:
% 0.61/0.86         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.61/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.86  thf('8', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.61/0.86      inference('sup-', [status(thm)], ['6', '7'])).
% 0.61/0.86  thf('9', plain,
% 0.61/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf(t44_tops_1, axiom,
% 0.61/0.86    (![A:$i]:
% 0.61/0.86     ( ( l1_pre_topc @ A ) =>
% 0.61/0.86       ( ![B:$i]:
% 0.61/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.86           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.61/0.86  thf('10', plain,
% 0.61/0.86      (![X13 : $i, X14 : $i]:
% 0.61/0.86         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.61/0.86          | (r1_tarski @ (k1_tops_1 @ X14 @ X13) @ X13)
% 0.61/0.86          | ~ (l1_pre_topc @ X14))),
% 0.61/0.86      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.61/0.86  thf('11', plain,
% 0.61/0.86      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.61/0.86      inference('sup-', [status(thm)], ['9', '10'])).
% 0.61/0.86  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('13', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.61/0.86      inference('demod', [status(thm)], ['11', '12'])).
% 0.61/0.86  thf(t1_xboole_1, axiom,
% 0.61/0.86    (![A:$i,B:$i,C:$i]:
% 0.61/0.86     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.61/0.86       ( r1_tarski @ A @ C ) ))).
% 0.61/0.86  thf('14', plain,
% 0.61/0.86      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.61/0.86         (~ (r1_tarski @ X3 @ X4)
% 0.61/0.86          | ~ (r1_tarski @ X4 @ X5)
% 0.61/0.86          | (r1_tarski @ X3 @ X5))),
% 0.61/0.86      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.61/0.86  thf('15', plain,
% 0.61/0.86      (![X0 : $i]:
% 0.61/0.86         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.61/0.86          | ~ (r1_tarski @ sk_B @ X0))),
% 0.61/0.86      inference('sup-', [status(thm)], ['13', '14'])).
% 0.61/0.86  thf('16', plain,
% 0.61/0.86      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.61/0.86      inference('sup-', [status(thm)], ['8', '15'])).
% 0.61/0.86  thf('17', plain,
% 0.61/0.86      (![X8 : $i, X10 : $i]:
% 0.61/0.86         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.61/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.86  thf('18', plain,
% 0.61/0.86      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.61/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.86      inference('sup-', [status(thm)], ['16', '17'])).
% 0.61/0.86  thf('19', plain,
% 0.61/0.86      ((![X20 : $i]:
% 0.61/0.86          (((X20) = (k1_xboole_0))
% 0.61/0.86           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.86           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.61/0.86           | ~ (r1_tarski @ X20 @ sk_B)))
% 0.61/0.86         <= ((![X20 : $i]:
% 0.61/0.86                (((X20) = (k1_xboole_0))
% 0.61/0.86                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.86                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.61/0.86                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.61/0.86      inference('split', [status(esa)], ['4'])).
% 0.61/0.86  thf('20', plain,
% 0.61/0.86      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.61/0.86         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.61/0.86         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.61/0.86         <= ((![X20 : $i]:
% 0.61/0.86                (((X20) = (k1_xboole_0))
% 0.61/0.86                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.86                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.61/0.86                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.61/0.86      inference('sup-', [status(thm)], ['18', '19'])).
% 0.61/0.86  thf('21', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.61/0.86      inference('demod', [status(thm)], ['11', '12'])).
% 0.61/0.86  thf('22', plain,
% 0.61/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf(fc9_tops_1, axiom,
% 0.61/0.86    (![A:$i,B:$i]:
% 0.61/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.61/0.86         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.61/0.86       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.61/0.86  thf('23', plain,
% 0.61/0.86      (![X11 : $i, X12 : $i]:
% 0.61/0.86         (~ (l1_pre_topc @ X11)
% 0.61/0.86          | ~ (v2_pre_topc @ X11)
% 0.61/0.86          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.61/0.86          | (v3_pre_topc @ (k1_tops_1 @ X11 @ X12) @ X11))),
% 0.61/0.86      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.61/0.86  thf('24', plain,
% 0.61/0.86      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.61/0.86        | ~ (v2_pre_topc @ sk_A)
% 0.61/0.86        | ~ (l1_pre_topc @ sk_A))),
% 0.61/0.86      inference('sup-', [status(thm)], ['22', '23'])).
% 0.61/0.86  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('27', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.61/0.86      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.61/0.86  thf('28', plain,
% 0.61/0.86      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.61/0.86         <= ((![X20 : $i]:
% 0.61/0.86                (((X20) = (k1_xboole_0))
% 0.61/0.86                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.86                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.61/0.86                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.61/0.86      inference('demod', [status(thm)], ['20', '21', '27'])).
% 0.61/0.86  thf('29', plain,
% 0.61/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf(t84_tops_1, axiom,
% 0.61/0.86    (![A:$i]:
% 0.61/0.86     ( ( l1_pre_topc @ A ) =>
% 0.61/0.86       ( ![B:$i]:
% 0.61/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.86           ( ( v2_tops_1 @ B @ A ) <=>
% 0.61/0.86             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.61/0.86  thf('30', plain,
% 0.61/0.86      (![X18 : $i, X19 : $i]:
% 0.61/0.86         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.61/0.86          | ((k1_tops_1 @ X19 @ X18) != (k1_xboole_0))
% 0.61/0.86          | (v2_tops_1 @ X18 @ X19)
% 0.61/0.86          | ~ (l1_pre_topc @ X19))),
% 0.61/0.86      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.61/0.86  thf('31', plain,
% 0.61/0.86      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.86        | (v2_tops_1 @ sk_B @ sk_A)
% 0.61/0.86        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.61/0.86      inference('sup-', [status(thm)], ['29', '30'])).
% 0.61/0.86  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('33', plain,
% 0.61/0.86      (((v2_tops_1 @ sk_B @ sk_A)
% 0.61/0.86        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.61/0.86      inference('demod', [status(thm)], ['31', '32'])).
% 0.61/0.86  thf('34', plain,
% 0.61/0.86      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.61/0.86         <= ((![X20 : $i]:
% 0.61/0.86                (((X20) = (k1_xboole_0))
% 0.61/0.86                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.86                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.61/0.86                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.61/0.86      inference('sup-', [status(thm)], ['28', '33'])).
% 0.61/0.86  thf('35', plain,
% 0.61/0.86      (((v2_tops_1 @ sk_B @ sk_A))
% 0.61/0.86         <= ((![X20 : $i]:
% 0.61/0.86                (((X20) = (k1_xboole_0))
% 0.61/0.86                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.86                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.61/0.86                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.61/0.86      inference('simplify', [status(thm)], ['34'])).
% 0.61/0.86  thf('36', plain,
% 0.61/0.86      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.61/0.86      inference('split', [status(esa)], ['2'])).
% 0.61/0.86  thf('37', plain,
% 0.61/0.86      (~
% 0.61/0.86       (![X20 : $i]:
% 0.61/0.86          (((X20) = (k1_xboole_0))
% 0.61/0.86           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.86           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.61/0.86           | ~ (r1_tarski @ X20 @ sk_B))) | 
% 0.61/0.86       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.86      inference('sup-', [status(thm)], ['35', '36'])).
% 0.61/0.86  thf('38', plain,
% 0.61/0.86      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('39', plain,
% 0.61/0.86      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.86      inference('split', [status(esa)], ['38'])).
% 0.61/0.86  thf('40', plain,
% 0.61/0.86      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.61/0.86      inference('split', [status(esa)], ['4'])).
% 0.61/0.86  thf('41', plain,
% 0.61/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('42', plain,
% 0.61/0.86      (![X18 : $i, X19 : $i]:
% 0.61/0.86         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.61/0.86          | ~ (v2_tops_1 @ X18 @ X19)
% 0.61/0.86          | ((k1_tops_1 @ X19 @ X18) = (k1_xboole_0))
% 0.61/0.86          | ~ (l1_pre_topc @ X19))),
% 0.61/0.86      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.61/0.86  thf('43', plain,
% 0.61/0.86      ((~ (l1_pre_topc @ sk_A)
% 0.61/0.86        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.61/0.86        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.86      inference('sup-', [status(thm)], ['41', '42'])).
% 0.61/0.86  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('45', plain,
% 0.61/0.86      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.61/0.86        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.61/0.86      inference('demod', [status(thm)], ['43', '44'])).
% 0.61/0.86  thf('46', plain,
% 0.61/0.86      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.61/0.86         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.61/0.86      inference('sup-', [status(thm)], ['40', '45'])).
% 0.61/0.86  thf('47', plain,
% 0.61/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('48', plain,
% 0.61/0.86      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.61/0.86      inference('split', [status(esa)], ['38'])).
% 0.61/0.86  thf('49', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.61/0.86      inference('sup-', [status(thm)], ['6', '7'])).
% 0.61/0.86  thf('50', plain,
% 0.61/0.86      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.61/0.86      inference('split', [status(esa)], ['2'])).
% 0.61/0.86  thf('51', plain,
% 0.61/0.86      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.61/0.86         (~ (r1_tarski @ X3 @ X4)
% 0.61/0.86          | ~ (r1_tarski @ X4 @ X5)
% 0.61/0.86          | (r1_tarski @ X3 @ X5))),
% 0.61/0.86      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.61/0.86  thf('52', plain,
% 0.61/0.86      ((![X0 : $i]: ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ sk_B @ X0)))
% 0.61/0.86         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.61/0.86      inference('sup-', [status(thm)], ['50', '51'])).
% 0.61/0.86  thf('53', plain,
% 0.61/0.86      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.61/0.86         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.61/0.86      inference('sup-', [status(thm)], ['49', '52'])).
% 0.61/0.86  thf('54', plain,
% 0.61/0.86      (![X8 : $i, X10 : $i]:
% 0.61/0.86         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.61/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.86  thf('55', plain,
% 0.61/0.86      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.61/0.86         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.61/0.86      inference('sup-', [status(thm)], ['53', '54'])).
% 0.61/0.86  thf(t56_tops_1, axiom,
% 0.61/0.86    (![A:$i]:
% 0.61/0.86     ( ( l1_pre_topc @ A ) =>
% 0.61/0.86       ( ![B:$i]:
% 0.61/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.86           ( ![C:$i]:
% 0.61/0.86             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.61/0.86               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.61/0.86                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.61/0.86  thf('56', plain,
% 0.61/0.86      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.61/0.86         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.61/0.86          | ~ (v3_pre_topc @ X15 @ X16)
% 0.61/0.86          | ~ (r1_tarski @ X15 @ X17)
% 0.61/0.86          | (r1_tarski @ X15 @ (k1_tops_1 @ X16 @ X17))
% 0.61/0.86          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.61/0.86          | ~ (l1_pre_topc @ X16))),
% 0.61/0.86      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.61/0.86  thf('57', plain,
% 0.61/0.86      ((![X0 : $i]:
% 0.61/0.86          (~ (l1_pre_topc @ sk_A)
% 0.61/0.86           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.86           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.61/0.86           | ~ (r1_tarski @ sk_C @ X0)
% 0.61/0.86           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.61/0.86         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.61/0.86      inference('sup-', [status(thm)], ['55', '56'])).
% 0.61/0.86  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('59', plain,
% 0.61/0.86      ((![X0 : $i]:
% 0.61/0.86          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.61/0.86           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.61/0.86           | ~ (r1_tarski @ sk_C @ X0)
% 0.61/0.86           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.61/0.86         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.61/0.86      inference('demod', [status(thm)], ['57', '58'])).
% 0.61/0.86  thf('60', plain,
% 0.61/0.86      ((![X0 : $i]:
% 0.61/0.86          (~ (r1_tarski @ sk_C @ X0)
% 0.61/0.86           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.61/0.86           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.61/0.86         <= (((r1_tarski @ sk_C @ sk_B)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.61/0.86      inference('sup-', [status(thm)], ['48', '59'])).
% 0.61/0.86  thf('61', plain,
% 0.61/0.86      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))
% 0.61/0.86         | ~ (r1_tarski @ sk_C @ sk_B)))
% 0.61/0.86         <= (((r1_tarski @ sk_C @ sk_B)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.61/0.86      inference('sup-', [status(thm)], ['47', '60'])).
% 0.61/0.86  thf('62', plain,
% 0.61/0.86      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.61/0.86      inference('split', [status(esa)], ['2'])).
% 0.61/0.86  thf('63', plain,
% 0.61/0.86      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.61/0.86         <= (((r1_tarski @ sk_C @ sk_B)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.61/0.86      inference('demod', [status(thm)], ['61', '62'])).
% 0.61/0.86  thf('64', plain,
% 0.61/0.86      (((r1_tarski @ sk_C @ k1_xboole_0))
% 0.61/0.86         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.61/0.86             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.61/0.86             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.61/0.86      inference('sup+', [status(thm)], ['46', '63'])).
% 0.61/0.86  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.61/0.86  thf('65', plain, (![X6 : $i]: ((k1_subset_1 @ X6) = (k1_xboole_0))),
% 0.61/0.86      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.61/0.86  thf(dt_k1_subset_1, axiom,
% 0.61/0.86    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.61/0.86  thf('66', plain,
% 0.61/0.86      (![X7 : $i]: (m1_subset_1 @ (k1_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.61/0.86      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 0.61/0.86  thf('67', plain,
% 0.61/0.86      (![X8 : $i, X9 : $i]:
% 0.61/0.86         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.61/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.86  thf('68', plain, (![X0 : $i]: (r1_tarski @ (k1_subset_1 @ X0) @ X0)),
% 0.61/0.86      inference('sup-', [status(thm)], ['66', '67'])).
% 0.61/0.86  thf('69', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.61/0.86      inference('sup+', [status(thm)], ['65', '68'])).
% 0.61/0.86  thf(d10_xboole_0, axiom,
% 0.61/0.86    (![A:$i,B:$i]:
% 0.61/0.86     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.86  thf('70', plain,
% 0.61/0.86      (![X0 : $i, X2 : $i]:
% 0.61/0.86         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.61/0.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.86  thf('71', plain,
% 0.61/0.86      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.61/0.86      inference('sup-', [status(thm)], ['69', '70'])).
% 0.61/0.86  thf('72', plain,
% 0.61/0.86      ((((sk_C) = (k1_xboole_0)))
% 0.61/0.86         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.61/0.86             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.61/0.86             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.61/0.86      inference('sup-', [status(thm)], ['64', '71'])).
% 0.61/0.86  thf('73', plain,
% 0.61/0.86      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.61/0.86      inference('split', [status(esa)], ['0'])).
% 0.61/0.86  thf('74', plain,
% 0.61/0.86      ((((sk_C) != (sk_C)))
% 0.61/0.86         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.61/0.86             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.61/0.86             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.61/0.86             ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.61/0.86      inference('sup-', [status(thm)], ['72', '73'])).
% 0.61/0.86  thf('75', plain,
% 0.61/0.86      (~ ((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.61/0.86       ~ ((r1_tarski @ sk_C @ sk_B)) | (((sk_C) = (k1_xboole_0)))),
% 0.61/0.86      inference('simplify', [status(thm)], ['74'])).
% 0.61/0.86  thf('76', plain, ($false),
% 0.61/0.86      inference('sat_resolution*', [status(thm)],
% 0.61/0.86                ['1', '3', '5', '37', '39', '75'])).
% 0.61/0.86  
% 0.61/0.86  % SZS output end Refutation
% 0.61/0.86  
% 0.69/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
