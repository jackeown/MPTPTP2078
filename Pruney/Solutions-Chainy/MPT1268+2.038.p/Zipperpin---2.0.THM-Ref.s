%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9LiXIXPKCe

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:21 EST 2020

% Result     : Theorem 1.08s
% Output     : Refutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 171 expanded)
%              Number of leaves         :   28 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  909 (2344 expanded)
%              Number of equality atoms :   39 (  93 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X41: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X41 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X41 @ sk_A )
      | ~ ( r1_tarski @ X41 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X41: $i] :
        ( ( X41 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X41 @ sk_A )
        | ~ ( r1_tarski @ X41 @ sk_B ) )
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
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X35 @ X34 ) @ X34 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
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
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X41: $i] :
        ( ( X41 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X41 @ sk_A )
        | ~ ( r1_tarski @ X41 @ sk_B ) )
   <= ! [X41: $i] :
        ( ( X41 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X41 @ sk_A )
        | ~ ( r1_tarski @ X41 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X41: $i] :
        ( ( X41 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X41 @ sk_A )
        | ~ ( r1_tarski @ X41 @ sk_B ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X32 @ X33 ) @ X32 ) ) ),
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
   <= ! [X41: $i] :
        ( ( X41 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X41 @ sk_A )
        | ~ ( r1_tarski @ X41 @ sk_B ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k1_tops_1 @ X40 @ X39 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
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
   <= ! [X41: $i] :
        ( ( X41 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X41 @ sk_A )
        | ~ ( r1_tarski @ X41 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X41: $i] :
        ( ( X41 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X41 @ sk_A )
        | ~ ( r1_tarski @ X41 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ~ ! [X41: $i] :
          ( ( X41 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X41 @ sk_A )
          | ~ ( r1_tarski @ X41 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('36',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
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
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v2_tops_1 @ X39 @ X40 )
      | ( ( k1_tops_1 @ X40 @ X39 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
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
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['32'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v3_pre_topc @ X36 @ X37 )
      | ~ ( r1_tarski @ X36 @ X38 )
      | ( r1_tarski @ X36 @ ( k1_tops_1 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C_1 @ X0 )
        | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C_1 @ X0 )
        | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C_1 @ X0 )
        | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_C_1 @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['48','59'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('61',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('62',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ X18 )
      | ( ( k4_xboole_0 @ X16 @ X18 )
       != X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('65',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('66',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','71'])).

thf('73',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('74',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( sk_C_1 != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','34','35','37','39','41','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9LiXIXPKCe
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.08/1.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.08/1.31  % Solved by: fo/fo7.sh
% 1.08/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.08/1.31  % done 3350 iterations in 0.835s
% 1.08/1.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.08/1.31  % SZS output start Refutation
% 1.08/1.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.08/1.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.08/1.31  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.08/1.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.08/1.31  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.08/1.31  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.08/1.31  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.08/1.31  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.08/1.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.08/1.31  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.08/1.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.08/1.31  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.08/1.31  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.08/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.08/1.31  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.08/1.31  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 1.08/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.08/1.31  thf(t86_tops_1, conjecture,
% 1.08/1.31    (![A:$i]:
% 1.08/1.31     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.08/1.31       ( ![B:$i]:
% 1.08/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.08/1.31           ( ( v2_tops_1 @ B @ A ) <=>
% 1.08/1.31             ( ![C:$i]:
% 1.08/1.31               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.08/1.31                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 1.08/1.31                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 1.08/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.08/1.31    (~( ![A:$i]:
% 1.08/1.31        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.08/1.31          ( ![B:$i]:
% 1.08/1.31            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.08/1.31              ( ( v2_tops_1 @ B @ A ) <=>
% 1.08/1.31                ( ![C:$i]:
% 1.08/1.31                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.08/1.31                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 1.08/1.31                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 1.08/1.31    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 1.08/1.31  thf('0', plain,
% 1.08/1.31      (![X41 : $i]:
% 1.08/1.31         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.08/1.31          | ((X41) = (k1_xboole_0))
% 1.08/1.31          | ~ (v3_pre_topc @ X41 @ sk_A)
% 1.08/1.31          | ~ (r1_tarski @ X41 @ sk_B)
% 1.08/1.31          | (v2_tops_1 @ sk_B @ sk_A))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('1', plain,
% 1.08/1.31      ((![X41 : $i]:
% 1.08/1.31          (((X41) = (k1_xboole_0))
% 1.08/1.31           | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.08/1.31           | ~ (v3_pre_topc @ X41 @ sk_A)
% 1.08/1.31           | ~ (r1_tarski @ X41 @ sk_B))) | 
% 1.08/1.31       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.08/1.31      inference('split', [status(esa)], ['0'])).
% 1.08/1.31  thf('2', plain,
% 1.08/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf(t3_subset, axiom,
% 1.08/1.31    (![A:$i,B:$i]:
% 1.08/1.31     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.08/1.31  thf('3', plain,
% 1.08/1.31      (![X26 : $i, X27 : $i]:
% 1.08/1.31         ((r1_tarski @ X26 @ X27) | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 1.08/1.31      inference('cnf', [status(esa)], [t3_subset])).
% 1.08/1.31  thf('4', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.08/1.31      inference('sup-', [status(thm)], ['2', '3'])).
% 1.08/1.31  thf('5', plain,
% 1.08/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf(t44_tops_1, axiom,
% 1.08/1.31    (![A:$i]:
% 1.08/1.31     ( ( l1_pre_topc @ A ) =>
% 1.08/1.31       ( ![B:$i]:
% 1.08/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.08/1.31           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.08/1.31  thf('6', plain,
% 1.08/1.31      (![X34 : $i, X35 : $i]:
% 1.08/1.31         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 1.08/1.31          | (r1_tarski @ (k1_tops_1 @ X35 @ X34) @ X34)
% 1.08/1.31          | ~ (l1_pre_topc @ X35))),
% 1.08/1.31      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.08/1.31  thf('7', plain,
% 1.08/1.31      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.08/1.31      inference('sup-', [status(thm)], ['5', '6'])).
% 1.08/1.31  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('9', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.08/1.31      inference('demod', [status(thm)], ['7', '8'])).
% 1.08/1.31  thf(t1_xboole_1, axiom,
% 1.08/1.31    (![A:$i,B:$i,C:$i]:
% 1.08/1.31     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.08/1.31       ( r1_tarski @ A @ C ) ))).
% 1.08/1.31  thf('10', plain,
% 1.08/1.31      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.08/1.31         (~ (r1_tarski @ X4 @ X5)
% 1.08/1.31          | ~ (r1_tarski @ X5 @ X6)
% 1.08/1.31          | (r1_tarski @ X4 @ X6))),
% 1.08/1.31      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.08/1.31  thf('11', plain,
% 1.08/1.31      (![X0 : $i]:
% 1.08/1.31         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.08/1.31          | ~ (r1_tarski @ sk_B @ X0))),
% 1.08/1.31      inference('sup-', [status(thm)], ['9', '10'])).
% 1.08/1.31  thf('12', plain,
% 1.08/1.31      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.08/1.31      inference('sup-', [status(thm)], ['4', '11'])).
% 1.08/1.31  thf('13', plain,
% 1.08/1.31      (![X26 : $i, X28 : $i]:
% 1.08/1.31         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 1.08/1.31      inference('cnf', [status(esa)], [t3_subset])).
% 1.08/1.31  thf('14', plain,
% 1.08/1.31      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.08/1.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.08/1.31      inference('sup-', [status(thm)], ['12', '13'])).
% 1.08/1.31  thf('15', plain,
% 1.08/1.31      ((![X41 : $i]:
% 1.08/1.31          (((X41) = (k1_xboole_0))
% 1.08/1.31           | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.08/1.31           | ~ (v3_pre_topc @ X41 @ sk_A)
% 1.08/1.31           | ~ (r1_tarski @ X41 @ sk_B)))
% 1.08/1.31         <= ((![X41 : $i]:
% 1.08/1.31                (((X41) = (k1_xboole_0))
% 1.08/1.31                 | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.08/1.31                 | ~ (v3_pre_topc @ X41 @ sk_A)
% 1.08/1.31                 | ~ (r1_tarski @ X41 @ sk_B))))),
% 1.08/1.31      inference('split', [status(esa)], ['0'])).
% 1.08/1.31  thf('16', plain,
% 1.08/1.31      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.08/1.31         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.08/1.31         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 1.08/1.31         <= ((![X41 : $i]:
% 1.08/1.31                (((X41) = (k1_xboole_0))
% 1.08/1.31                 | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.08/1.31                 | ~ (v3_pre_topc @ X41 @ sk_A)
% 1.08/1.31                 | ~ (r1_tarski @ X41 @ sk_B))))),
% 1.08/1.31      inference('sup-', [status(thm)], ['14', '15'])).
% 1.08/1.31  thf('17', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.08/1.31      inference('demod', [status(thm)], ['7', '8'])).
% 1.08/1.31  thf('18', plain,
% 1.08/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf(fc9_tops_1, axiom,
% 1.08/1.31    (![A:$i,B:$i]:
% 1.08/1.31     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.08/1.31         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.08/1.31       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.08/1.31  thf('19', plain,
% 1.08/1.31      (![X32 : $i, X33 : $i]:
% 1.08/1.31         (~ (l1_pre_topc @ X32)
% 1.08/1.31          | ~ (v2_pre_topc @ X32)
% 1.08/1.31          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.08/1.31          | (v3_pre_topc @ (k1_tops_1 @ X32 @ X33) @ X32))),
% 1.08/1.31      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.08/1.31  thf('20', plain,
% 1.08/1.31      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.08/1.31        | ~ (v2_pre_topc @ sk_A)
% 1.08/1.31        | ~ (l1_pre_topc @ sk_A))),
% 1.08/1.31      inference('sup-', [status(thm)], ['18', '19'])).
% 1.08/1.31  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('23', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.08/1.31      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.08/1.31  thf('24', plain,
% 1.08/1.31      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.08/1.31         <= ((![X41 : $i]:
% 1.08/1.31                (((X41) = (k1_xboole_0))
% 1.08/1.31                 | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.08/1.31                 | ~ (v3_pre_topc @ X41 @ sk_A)
% 1.08/1.31                 | ~ (r1_tarski @ X41 @ sk_B))))),
% 1.08/1.31      inference('demod', [status(thm)], ['16', '17', '23'])).
% 1.08/1.31  thf('25', plain,
% 1.08/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf(t84_tops_1, axiom,
% 1.08/1.31    (![A:$i]:
% 1.08/1.31     ( ( l1_pre_topc @ A ) =>
% 1.08/1.31       ( ![B:$i]:
% 1.08/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.08/1.31           ( ( v2_tops_1 @ B @ A ) <=>
% 1.08/1.31             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.08/1.31  thf('26', plain,
% 1.08/1.31      (![X39 : $i, X40 : $i]:
% 1.08/1.31         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.08/1.31          | ((k1_tops_1 @ X40 @ X39) != (k1_xboole_0))
% 1.08/1.31          | (v2_tops_1 @ X39 @ X40)
% 1.08/1.31          | ~ (l1_pre_topc @ X40))),
% 1.08/1.31      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.08/1.31  thf('27', plain,
% 1.08/1.31      ((~ (l1_pre_topc @ sk_A)
% 1.08/1.31        | (v2_tops_1 @ sk_B @ sk_A)
% 1.08/1.31        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 1.08/1.31      inference('sup-', [status(thm)], ['25', '26'])).
% 1.08/1.31  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('29', plain,
% 1.08/1.31      (((v2_tops_1 @ sk_B @ sk_A)
% 1.08/1.31        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 1.08/1.31      inference('demod', [status(thm)], ['27', '28'])).
% 1.08/1.31  thf('30', plain,
% 1.08/1.31      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 1.08/1.31         <= ((![X41 : $i]:
% 1.08/1.31                (((X41) = (k1_xboole_0))
% 1.08/1.31                 | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.08/1.31                 | ~ (v3_pre_topc @ X41 @ sk_A)
% 1.08/1.31                 | ~ (r1_tarski @ X41 @ sk_B))))),
% 1.08/1.31      inference('sup-', [status(thm)], ['24', '29'])).
% 1.08/1.31  thf('31', plain,
% 1.08/1.31      (((v2_tops_1 @ sk_B @ sk_A))
% 1.08/1.31         <= ((![X41 : $i]:
% 1.08/1.31                (((X41) = (k1_xboole_0))
% 1.08/1.31                 | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.08/1.31                 | ~ (v3_pre_topc @ X41 @ sk_A)
% 1.08/1.31                 | ~ (r1_tarski @ X41 @ sk_B))))),
% 1.08/1.31      inference('simplify', [status(thm)], ['30'])).
% 1.08/1.31  thf('32', plain,
% 1.08/1.31      (((r1_tarski @ sk_C_1 @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('33', plain,
% 1.08/1.31      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 1.08/1.31      inference('split', [status(esa)], ['32'])).
% 1.08/1.31  thf('34', plain,
% 1.08/1.31      (~
% 1.08/1.31       (![X41 : $i]:
% 1.08/1.31          (((X41) = (k1_xboole_0))
% 1.08/1.31           | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.08/1.31           | ~ (v3_pre_topc @ X41 @ sk_A)
% 1.08/1.31           | ~ (r1_tarski @ X41 @ sk_B))) | 
% 1.08/1.31       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.08/1.31      inference('sup-', [status(thm)], ['31', '33'])).
% 1.08/1.31  thf('35', plain,
% 1.08/1.31      (((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.08/1.31      inference('split', [status(esa)], ['32'])).
% 1.08/1.31  thf('36', plain,
% 1.08/1.31      (((v3_pre_topc @ sk_C_1 @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('37', plain,
% 1.08/1.31      (((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.08/1.31      inference('split', [status(esa)], ['36'])).
% 1.08/1.31  thf('38', plain,
% 1.08/1.31      ((((sk_C_1) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('39', plain,
% 1.08/1.31      (~ (((sk_C_1) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.08/1.31      inference('split', [status(esa)], ['38'])).
% 1.08/1.31  thf('40', plain,
% 1.08/1.31      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.08/1.31        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('41', plain,
% 1.08/1.31      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 1.08/1.31       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.08/1.31      inference('split', [status(esa)], ['40'])).
% 1.08/1.31  thf('42', plain,
% 1.08/1.31      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.08/1.31      inference('split', [status(esa)], ['0'])).
% 1.08/1.31  thf('43', plain,
% 1.08/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('44', plain,
% 1.08/1.31      (![X39 : $i, X40 : $i]:
% 1.08/1.31         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.08/1.31          | ~ (v2_tops_1 @ X39 @ X40)
% 1.08/1.31          | ((k1_tops_1 @ X40 @ X39) = (k1_xboole_0))
% 1.08/1.31          | ~ (l1_pre_topc @ X40))),
% 1.08/1.31      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.08/1.31  thf('45', plain,
% 1.08/1.31      ((~ (l1_pre_topc @ sk_A)
% 1.08/1.31        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.08/1.31        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.08/1.31      inference('sup-', [status(thm)], ['43', '44'])).
% 1.08/1.31  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('47', plain,
% 1.08/1.31      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.08/1.31        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.08/1.31      inference('demod', [status(thm)], ['45', '46'])).
% 1.08/1.31  thf('48', plain,
% 1.08/1.31      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.08/1.31         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.08/1.31      inference('sup-', [status(thm)], ['42', '47'])).
% 1.08/1.31  thf('49', plain,
% 1.08/1.31      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 1.08/1.31      inference('split', [status(esa)], ['32'])).
% 1.08/1.31  thf('50', plain,
% 1.08/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('51', plain,
% 1.08/1.31      (((v3_pre_topc @ sk_C_1 @ sk_A)) <= (((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 1.08/1.31      inference('split', [status(esa)], ['36'])).
% 1.08/1.31  thf('52', plain,
% 1.08/1.31      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.08/1.31         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.08/1.31      inference('split', [status(esa)], ['40'])).
% 1.08/1.31  thf(t56_tops_1, axiom,
% 1.08/1.31    (![A:$i]:
% 1.08/1.31     ( ( l1_pre_topc @ A ) =>
% 1.08/1.31       ( ![B:$i]:
% 1.08/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.08/1.31           ( ![C:$i]:
% 1.08/1.31             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.08/1.31               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.08/1.31                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.08/1.31  thf('53', plain,
% 1.08/1.31      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.08/1.31         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.08/1.31          | ~ (v3_pre_topc @ X36 @ X37)
% 1.08/1.31          | ~ (r1_tarski @ X36 @ X38)
% 1.08/1.31          | (r1_tarski @ X36 @ (k1_tops_1 @ X37 @ X38))
% 1.08/1.31          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.08/1.31          | ~ (l1_pre_topc @ X37))),
% 1.08/1.31      inference('cnf', [status(esa)], [t56_tops_1])).
% 1.08/1.31  thf('54', plain,
% 1.08/1.31      ((![X0 : $i]:
% 1.08/1.31          (~ (l1_pre_topc @ sk_A)
% 1.08/1.31           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.08/1.31           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 1.08/1.31           | ~ (r1_tarski @ sk_C_1 @ X0)
% 1.08/1.31           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)))
% 1.08/1.31         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.08/1.31      inference('sup-', [status(thm)], ['52', '53'])).
% 1.08/1.31  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('56', plain,
% 1.08/1.31      ((![X0 : $i]:
% 1.08/1.31          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.08/1.31           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 1.08/1.31           | ~ (r1_tarski @ sk_C_1 @ X0)
% 1.08/1.31           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)))
% 1.08/1.31         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.08/1.31      inference('demod', [status(thm)], ['54', '55'])).
% 1.08/1.31  thf('57', plain,
% 1.08/1.31      ((![X0 : $i]:
% 1.08/1.31          (~ (r1_tarski @ sk_C_1 @ X0)
% 1.08/1.31           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 1.08/1.31           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.08/1.31         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.08/1.31             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.08/1.31      inference('sup-', [status(thm)], ['51', '56'])).
% 1.08/1.31  thf('58', plain,
% 1.08/1.31      ((((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B))
% 1.08/1.31         | ~ (r1_tarski @ sk_C_1 @ sk_B)))
% 1.08/1.31         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.08/1.31             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.08/1.31      inference('sup-', [status(thm)], ['50', '57'])).
% 1.08/1.31  thf('59', plain,
% 1.08/1.31      (((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.08/1.31         <= (((r1_tarski @ sk_C_1 @ sk_B)) & 
% 1.08/1.31             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.08/1.31             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.08/1.31      inference('sup-', [status(thm)], ['49', '58'])).
% 1.08/1.31  thf('60', plain,
% 1.08/1.31      (((r1_tarski @ sk_C_1 @ k1_xboole_0))
% 1.08/1.31         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 1.08/1.31             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 1.08/1.31             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.08/1.31             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.08/1.31      inference('sup+', [status(thm)], ['48', '59'])).
% 1.08/1.31  thf(t3_boole, axiom,
% 1.08/1.31    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.08/1.31  thf('61', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.08/1.31      inference('cnf', [status(esa)], [t3_boole])).
% 1.08/1.31  thf(t83_xboole_1, axiom,
% 1.08/1.31    (![A:$i,B:$i]:
% 1.08/1.31     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.08/1.31  thf('62', plain,
% 1.08/1.31      (![X16 : $i, X18 : $i]:
% 1.08/1.31         ((r1_xboole_0 @ X16 @ X18) | ((k4_xboole_0 @ X16 @ X18) != (X16)))),
% 1.08/1.31      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.08/1.31  thf('63', plain,
% 1.08/1.31      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.08/1.31      inference('sup-', [status(thm)], ['61', '62'])).
% 1.08/1.31  thf('64', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.08/1.31      inference('simplify', [status(thm)], ['63'])).
% 1.08/1.31  thf(d3_tarski, axiom,
% 1.08/1.31    (![A:$i,B:$i]:
% 1.08/1.31     ( ( r1_tarski @ A @ B ) <=>
% 1.08/1.31       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.08/1.31  thf('65', plain,
% 1.08/1.31      (![X1 : $i, X3 : $i]:
% 1.08/1.31         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.08/1.31      inference('cnf', [status(esa)], [d3_tarski])).
% 1.08/1.31  thf('66', plain,
% 1.08/1.31      (![X1 : $i, X3 : $i]:
% 1.08/1.31         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.08/1.31      inference('cnf', [status(esa)], [d3_tarski])).
% 1.08/1.31  thf('67', plain,
% 1.08/1.31      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.08/1.31      inference('sup-', [status(thm)], ['65', '66'])).
% 1.08/1.31  thf('68', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.08/1.31      inference('simplify', [status(thm)], ['67'])).
% 1.08/1.31  thf(t67_xboole_1, axiom,
% 1.08/1.31    (![A:$i,B:$i,C:$i]:
% 1.08/1.31     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 1.08/1.31         ( r1_xboole_0 @ B @ C ) ) =>
% 1.08/1.31       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.08/1.31  thf('69', plain,
% 1.08/1.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.08/1.31         (((X13) = (k1_xboole_0))
% 1.08/1.31          | ~ (r1_tarski @ X13 @ X14)
% 1.08/1.31          | ~ (r1_tarski @ X13 @ X15)
% 1.08/1.31          | ~ (r1_xboole_0 @ X14 @ X15))),
% 1.08/1.31      inference('cnf', [status(esa)], [t67_xboole_1])).
% 1.08/1.31  thf('70', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i]:
% 1.08/1.31         (~ (r1_xboole_0 @ X0 @ X1)
% 1.08/1.31          | ~ (r1_tarski @ X0 @ X1)
% 1.08/1.31          | ((X0) = (k1_xboole_0)))),
% 1.08/1.31      inference('sup-', [status(thm)], ['68', '69'])).
% 1.08/1.31  thf('71', plain,
% 1.08/1.31      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 1.08/1.31      inference('sup-', [status(thm)], ['64', '70'])).
% 1.08/1.31  thf('72', plain,
% 1.08/1.31      ((((sk_C_1) = (k1_xboole_0)))
% 1.08/1.31         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 1.08/1.31             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 1.08/1.31             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.08/1.31             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.08/1.31      inference('sup-', [status(thm)], ['60', '71'])).
% 1.08/1.31  thf('73', plain,
% 1.08/1.31      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.08/1.31      inference('split', [status(esa)], ['38'])).
% 1.08/1.31  thf('74', plain,
% 1.08/1.31      ((((sk_C_1) != (sk_C_1)))
% 1.08/1.31         <= (~ (((sk_C_1) = (k1_xboole_0))) & 
% 1.08/1.31             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 1.08/1.31             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 1.08/1.31             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.08/1.31             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.08/1.31      inference('sup-', [status(thm)], ['72', '73'])).
% 1.08/1.31  thf('75', plain,
% 1.08/1.31      (~ ((v3_pre_topc @ sk_C_1 @ sk_A)) | 
% 1.08/1.31       ~ ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 1.08/1.31       ~ ((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 1.08/1.31       (((sk_C_1) = (k1_xboole_0)))),
% 1.08/1.31      inference('simplify', [status(thm)], ['74'])).
% 1.08/1.31  thf('76', plain, ($false),
% 1.08/1.31      inference('sat_resolution*', [status(thm)],
% 1.08/1.31                ['1', '34', '35', '37', '39', '41', '75'])).
% 1.08/1.31  
% 1.08/1.31  % SZS output end Refutation
% 1.08/1.31  
% 1.08/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
