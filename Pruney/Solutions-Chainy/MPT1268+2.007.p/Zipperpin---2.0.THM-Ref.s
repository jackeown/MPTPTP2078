%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tYHR2uk16Q

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:16 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 174 expanded)
%              Number of leaves         :   27 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  925 (2374 expanded)
%              Number of equality atoms :   43 (  99 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X25 @ sk_A )
      | ~ ( r1_tarski @ X25 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B ) )
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X16 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('20',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
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
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','23'])).

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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k1_tops_1 @ X24 @ X23 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B ) ) ),
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
    ( ~ ! [X25: $i] :
          ( ( X25 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X25 @ sk_A )
          | ~ ( r1_tarski @ X25 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('38',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tops_1 @ X23 @ X24 )
      | ( ( k1_tops_1 @ X24 @ X23 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['32'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['40'])).

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

thf('53',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X21 )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ( r1_tarski @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_C @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['48','59'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('61',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('62',plain,
    ( ( ( k3_xboole_0 @ sk_C @ k1_xboole_0 )
      = sk_C )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('64',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('68',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['62','73'])).

thf('75',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('76',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','34','36','37','39','41','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tYHR2uk16Q
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.82  % Solved by: fo/fo7.sh
% 0.58/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.82  % done 840 iterations in 0.363s
% 0.58/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.82  % SZS output start Refutation
% 0.58/0.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.82  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.58/0.82  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.58/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.82  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.58/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.82  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.82  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.58/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.82  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.58/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.82  thf(t86_tops_1, conjecture,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.82       ( ![B:$i]:
% 0.58/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.82           ( ( v2_tops_1 @ B @ A ) <=>
% 0.58/0.82             ( ![C:$i]:
% 0.58/0.82               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.82                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.58/0.82                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.82    (~( ![A:$i]:
% 0.58/0.82        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.82          ( ![B:$i]:
% 0.58/0.82            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.82              ( ( v2_tops_1 @ B @ A ) <=>
% 0.58/0.82                ( ![C:$i]:
% 0.58/0.82                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.82                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.58/0.82                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.58/0.82    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.58/0.82  thf('0', plain,
% 0.58/0.82      (![X25 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.82          | ((X25) = (k1_xboole_0))
% 0.58/0.82          | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.58/0.82          | ~ (r1_tarski @ X25 @ sk_B)
% 0.58/0.82          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('1', plain,
% 0.58/0.82      ((![X25 : $i]:
% 0.58/0.82          (((X25) = (k1_xboole_0))
% 0.58/0.82           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.82           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.58/0.82           | ~ (r1_tarski @ X25 @ sk_B))) | 
% 0.58/0.82       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('split', [status(esa)], ['0'])).
% 0.58/0.82  thf('2', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(t3_subset, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.82  thf('3', plain,
% 0.58/0.82      (![X10 : $i, X11 : $i]:
% 0.58/0.82         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.82  thf('4', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.82  thf('5', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(t44_tops_1, axiom,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( l1_pre_topc @ A ) =>
% 0.58/0.82       ( ![B:$i]:
% 0.58/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.82           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.58/0.82  thf('6', plain,
% 0.58/0.82      (![X18 : $i, X19 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.58/0.82          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ X18)
% 0.58/0.82          | ~ (l1_pre_topc @ X19))),
% 0.58/0.82      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.58/0.82  thf('7', plain,
% 0.58/0.82      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.58/0.82      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.82  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('9', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.58/0.82      inference('demod', [status(thm)], ['7', '8'])).
% 0.58/0.82  thf(t1_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.58/0.82       ( r1_tarski @ A @ C ) ))).
% 0.58/0.82  thf('10', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         (~ (r1_tarski @ X0 @ X1)
% 0.58/0.82          | ~ (r1_tarski @ X1 @ X2)
% 0.58/0.82          | (r1_tarski @ X0 @ X2))),
% 0.58/0.82      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.58/0.82  thf('11', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.58/0.82          | ~ (r1_tarski @ sk_B @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['9', '10'])).
% 0.58/0.82  thf('12', plain,
% 0.58/0.82      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['4', '11'])).
% 0.58/0.82  thf('13', plain,
% 0.58/0.82      (![X10 : $i, X12 : $i]:
% 0.58/0.82         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.58/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.82  thf('14', plain,
% 0.58/0.82      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.58/0.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.82  thf('15', plain,
% 0.58/0.82      ((![X25 : $i]:
% 0.58/0.82          (((X25) = (k1_xboole_0))
% 0.58/0.82           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.82           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.58/0.82           | ~ (r1_tarski @ X25 @ sk_B)))
% 0.58/0.82         <= ((![X25 : $i]:
% 0.58/0.82                (((X25) = (k1_xboole_0))
% 0.58/0.82                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.82                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.58/0.82                 | ~ (r1_tarski @ X25 @ sk_B))))),
% 0.58/0.82      inference('split', [status(esa)], ['0'])).
% 0.58/0.82  thf('16', plain,
% 0.58/0.82      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.58/0.82         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.58/0.82         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.58/0.82         <= ((![X25 : $i]:
% 0.58/0.82                (((X25) = (k1_xboole_0))
% 0.58/0.82                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.82                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.58/0.82                 | ~ (r1_tarski @ X25 @ sk_B))))),
% 0.58/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.82  thf('17', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.58/0.82      inference('demod', [status(thm)], ['7', '8'])).
% 0.58/0.82  thf('18', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(fc9_tops_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.58/0.82         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.82       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.58/0.82  thf('19', plain,
% 0.58/0.82      (![X16 : $i, X17 : $i]:
% 0.58/0.82         (~ (l1_pre_topc @ X16)
% 0.58/0.82          | ~ (v2_pre_topc @ X16)
% 0.58/0.82          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.58/0.82          | (v3_pre_topc @ (k1_tops_1 @ X16 @ X17) @ X16))),
% 0.58/0.82      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.58/0.82  thf('20', plain,
% 0.58/0.82      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.58/0.82        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.82        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.82  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('23', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.58/0.82      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.58/0.82  thf('24', plain,
% 0.58/0.82      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.58/0.82         <= ((![X25 : $i]:
% 0.58/0.82                (((X25) = (k1_xboole_0))
% 0.58/0.82                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.82                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.58/0.82                 | ~ (r1_tarski @ X25 @ sk_B))))),
% 0.58/0.82      inference('demod', [status(thm)], ['16', '17', '23'])).
% 0.58/0.82  thf('25', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(t84_tops_1, axiom,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( l1_pre_topc @ A ) =>
% 0.58/0.82       ( ![B:$i]:
% 0.58/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.82           ( ( v2_tops_1 @ B @ A ) <=>
% 0.58/0.82             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.58/0.82  thf('26', plain,
% 0.58/0.82      (![X23 : $i, X24 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.58/0.82          | ((k1_tops_1 @ X24 @ X23) != (k1_xboole_0))
% 0.58/0.82          | (v2_tops_1 @ X23 @ X24)
% 0.58/0.82          | ~ (l1_pre_topc @ X24))),
% 0.58/0.82      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.58/0.82  thf('27', plain,
% 0.58/0.82      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.82        | (v2_tops_1 @ sk_B @ sk_A)
% 0.58/0.82        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.82  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('29', plain,
% 0.58/0.82      (((v2_tops_1 @ sk_B @ sk_A)
% 0.58/0.82        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['27', '28'])).
% 0.58/0.82  thf('30', plain,
% 0.58/0.82      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.58/0.82         <= ((![X25 : $i]:
% 0.58/0.82                (((X25) = (k1_xboole_0))
% 0.58/0.82                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.82                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.58/0.82                 | ~ (r1_tarski @ X25 @ sk_B))))),
% 0.58/0.82      inference('sup-', [status(thm)], ['24', '29'])).
% 0.58/0.82  thf('31', plain,
% 0.58/0.82      (((v2_tops_1 @ sk_B @ sk_A))
% 0.58/0.82         <= ((![X25 : $i]:
% 0.58/0.82                (((X25) = (k1_xboole_0))
% 0.58/0.82                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.82                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.58/0.82                 | ~ (r1_tarski @ X25 @ sk_B))))),
% 0.58/0.82      inference('simplify', [status(thm)], ['30'])).
% 0.58/0.82  thf('32', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('33', plain,
% 0.58/0.82      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.58/0.82      inference('split', [status(esa)], ['32'])).
% 0.58/0.82  thf('34', plain,
% 0.58/0.82      (~
% 0.58/0.82       (![X25 : $i]:
% 0.58/0.82          (((X25) = (k1_xboole_0))
% 0.58/0.82           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.82           | ~ (v3_pre_topc @ X25 @ sk_A)
% 0.58/0.82           | ~ (r1_tarski @ X25 @ sk_B))) | 
% 0.58/0.82       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['31', '33'])).
% 0.58/0.82  thf('35', plain,
% 0.58/0.82      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('36', plain,
% 0.58/0.82      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('split', [status(esa)], ['35'])).
% 0.58/0.82  thf('37', plain,
% 0.58/0.82      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('split', [status(esa)], ['32'])).
% 0.58/0.82  thf('38', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('39', plain,
% 0.58/0.82      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('split', [status(esa)], ['38'])).
% 0.58/0.82  thf('40', plain,
% 0.58/0.82      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.82        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('41', plain,
% 0.58/0.82      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.58/0.82       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('split', [status(esa)], ['40'])).
% 0.58/0.82  thf('42', plain,
% 0.58/0.82      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.58/0.82      inference('split', [status(esa)], ['0'])).
% 0.58/0.82  thf('43', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('44', plain,
% 0.58/0.82      (![X23 : $i, X24 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.58/0.82          | ~ (v2_tops_1 @ X23 @ X24)
% 0.58/0.82          | ((k1_tops_1 @ X24 @ X23) = (k1_xboole_0))
% 0.58/0.82          | ~ (l1_pre_topc @ X24))),
% 0.58/0.82      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.58/0.82  thf('45', plain,
% 0.58/0.82      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.82        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.58/0.82        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['43', '44'])).
% 0.58/0.82  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('47', plain,
% 0.58/0.82      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.58/0.82        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('demod', [status(thm)], ['45', '46'])).
% 0.58/0.82  thf('48', plain,
% 0.58/0.82      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.58/0.82         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['42', '47'])).
% 0.58/0.82  thf('49', plain,
% 0.58/0.82      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.58/0.82      inference('split', [status(esa)], ['32'])).
% 0.58/0.82  thf('50', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('51', plain,
% 0.58/0.82      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.58/0.82      inference('split', [status(esa)], ['35'])).
% 0.58/0.82  thf('52', plain,
% 0.58/0.82      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.58/0.82         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.58/0.82      inference('split', [status(esa)], ['40'])).
% 0.58/0.82  thf(t56_tops_1, axiom,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( l1_pre_topc @ A ) =>
% 0.58/0.82       ( ![B:$i]:
% 0.58/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.82           ( ![C:$i]:
% 0.58/0.82             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.82               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.58/0.82                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.58/0.82  thf('53', plain,
% 0.58/0.82      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.58/0.82          | ~ (v3_pre_topc @ X20 @ X21)
% 0.58/0.82          | ~ (r1_tarski @ X20 @ X22)
% 0.58/0.82          | (r1_tarski @ X20 @ (k1_tops_1 @ X21 @ X22))
% 0.58/0.82          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.58/0.82          | ~ (l1_pre_topc @ X21))),
% 0.58/0.82      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.58/0.82  thf('54', plain,
% 0.58/0.82      ((![X0 : $i]:
% 0.58/0.82          (~ (l1_pre_topc @ sk_A)
% 0.58/0.82           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.82           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.58/0.82           | ~ (r1_tarski @ sk_C @ X0)
% 0.58/0.82           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.58/0.82         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.58/0.82      inference('sup-', [status(thm)], ['52', '53'])).
% 0.58/0.82  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('56', plain,
% 0.58/0.82      ((![X0 : $i]:
% 0.58/0.82          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.82           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.58/0.82           | ~ (r1_tarski @ sk_C @ X0)
% 0.58/0.82           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.58/0.82         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.58/0.82      inference('demod', [status(thm)], ['54', '55'])).
% 0.58/0.82  thf('57', plain,
% 0.58/0.82      ((![X0 : $i]:
% 0.58/0.82          (~ (r1_tarski @ sk_C @ X0)
% 0.58/0.82           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.58/0.82           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.58/0.82         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.58/0.82             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.58/0.82      inference('sup-', [status(thm)], ['51', '56'])).
% 0.58/0.82  thf('58', plain,
% 0.58/0.82      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))
% 0.58/0.82         | ~ (r1_tarski @ sk_C @ sk_B)))
% 0.58/0.82         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.58/0.82             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.58/0.82      inference('sup-', [status(thm)], ['50', '57'])).
% 0.58/0.82  thf('59', plain,
% 0.58/0.82      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.58/0.82         <= (((r1_tarski @ sk_C @ sk_B)) & 
% 0.58/0.82             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.58/0.82             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.58/0.82      inference('sup-', [status(thm)], ['49', '58'])).
% 0.58/0.82  thf('60', plain,
% 0.58/0.82      (((r1_tarski @ sk_C @ k1_xboole_0))
% 0.58/0.82         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.58/0.82             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.58/0.82             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.58/0.82             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.58/0.82      inference('sup+', [status(thm)], ['48', '59'])).
% 0.58/0.82  thf(t28_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.58/0.82  thf('61', plain,
% 0.58/0.82      (![X3 : $i, X4 : $i]:
% 0.58/0.82         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.58/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.82  thf('62', plain,
% 0.58/0.82      ((((k3_xboole_0 @ sk_C @ k1_xboole_0) = (sk_C)))
% 0.58/0.82         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.58/0.82             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.58/0.82             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.58/0.82             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.58/0.82      inference('sup-', [status(thm)], ['60', '61'])).
% 0.58/0.82  thf(commutativity_k2_tarski, axiom,
% 0.58/0.82    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.58/0.82  thf('63', plain,
% 0.58/0.82      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.58/0.82      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.58/0.82  thf(t12_setfam_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.82  thf('64', plain,
% 0.58/0.82      (![X8 : $i, X9 : $i]:
% 0.58/0.82         ((k1_setfam_1 @ (k2_tarski @ X8 @ X9)) = (k3_xboole_0 @ X8 @ X9))),
% 0.58/0.82      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.58/0.82  thf('65', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.82      inference('sup+', [status(thm)], ['63', '64'])).
% 0.58/0.82  thf('66', plain,
% 0.58/0.82      (![X8 : $i, X9 : $i]:
% 0.58/0.82         ((k1_setfam_1 @ (k2_tarski @ X8 @ X9)) = (k3_xboole_0 @ X8 @ X9))),
% 0.58/0.82      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.58/0.82  thf('67', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.82      inference('sup+', [status(thm)], ['65', '66'])).
% 0.58/0.82  thf(t4_subset_1, axiom,
% 0.58/0.82    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.58/0.82  thf('68', plain,
% 0.58/0.82      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.58/0.82      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.58/0.82  thf('69', plain,
% 0.58/0.82      (![X10 : $i, X11 : $i]:
% 0.58/0.82         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.82  thf('70', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.82      inference('sup-', [status(thm)], ['68', '69'])).
% 0.58/0.82  thf('71', plain,
% 0.58/0.82      (![X3 : $i, X4 : $i]:
% 0.58/0.82         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.58/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.82  thf('72', plain,
% 0.58/0.82      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['70', '71'])).
% 0.58/0.82  thf('73', plain,
% 0.58/0.82      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['67', '72'])).
% 0.58/0.82  thf('74', plain,
% 0.58/0.82      ((((k1_xboole_0) = (sk_C)))
% 0.58/0.82         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.58/0.82             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.58/0.82             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.58/0.82             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.58/0.82      inference('demod', [status(thm)], ['62', '73'])).
% 0.58/0.82  thf('75', plain,
% 0.58/0.82      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.58/0.82      inference('split', [status(esa)], ['38'])).
% 0.58/0.82  thf('76', plain,
% 0.58/0.82      ((((sk_C) != (sk_C)))
% 0.58/0.82         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.58/0.82             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.58/0.82             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.58/0.82             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.58/0.82             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.58/0.82      inference('sup-', [status(thm)], ['74', '75'])).
% 0.58/0.82  thf('77', plain,
% 0.58/0.82      (~ ((r1_tarski @ sk_C @ sk_B)) | 
% 0.58/0.82       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.58/0.82       ~ ((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.58/0.82       (((sk_C) = (k1_xboole_0)))),
% 0.58/0.82      inference('simplify', [status(thm)], ['76'])).
% 0.58/0.82  thf('78', plain, ($false),
% 0.58/0.82      inference('sat_resolution*', [status(thm)],
% 0.58/0.82                ['1', '34', '36', '37', '39', '41', '77'])).
% 0.58/0.82  
% 0.58/0.82  % SZS output end Refutation
% 0.58/0.82  
% 0.58/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
