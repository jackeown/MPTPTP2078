%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YgnrP8cz06

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:17 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 334 expanded)
%              Number of leaves         :   32 ( 110 expanded)
%              Depth                    :   24
%              Number of atoms          : 1150 (3408 expanded)
%              Number of equality atoms :   43 ( 123 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X30 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X30 @ sk_A )
      | ~ ( r1_tarski @ X30 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B ) )
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
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X24 @ X23 ) @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
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
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B ) )
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X21 @ X22 ) @ X21 ) ) ),
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
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k1_tops_1 @ X29 @ X28 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
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
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B ) ) ),
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
    ( ~ ! [X30: $i] :
          ( ( X30 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X30 @ sk_A )
          | ~ ( r1_tarski @ X30 @ sk_B ) )
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tops_1 @ X28 @ X29 )
      | ( ( k1_tops_1 @ X29 @ X28 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X26 )
      | ~ ( r1_tarski @ X25 @ X27 )
      | ( r1_tarski @ X25 @ ( k1_tops_1 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('62',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('63',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X14 ) @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('64',plain,(
    ! [X13: $i] :
      ( ( k2_subset_1 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('65',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('66',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X24 @ X23 ) @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('73',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('74',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('77',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['76','80'])).

thf('82',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['78','79'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('86',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['76','80'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
        = ( k1_tops_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_tops_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference('sup-',[status(thm)],['82','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['81','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(condensation,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['61','104'])).

thf('106',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','107'])).

thf('109',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('110',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( sk_C_1 != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','34','35','37','39','41','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YgnrP8cz06
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:38:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.52/1.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.52/1.73  % Solved by: fo/fo7.sh
% 1.52/1.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.52/1.73  % done 3746 iterations in 1.268s
% 1.52/1.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.52/1.73  % SZS output start Refutation
% 1.52/1.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.52/1.73  thf(sk_A_type, type, sk_A: $i).
% 1.52/1.73  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.52/1.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.52/1.73  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.52/1.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.52/1.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.52/1.73  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 1.52/1.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.52/1.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.52/1.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.52/1.73  thf(sk_B_type, type, sk_B: $i).
% 1.52/1.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.52/1.73  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.52/1.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.52/1.73  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.52/1.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.52/1.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.52/1.73  thf(t86_tops_1, conjecture,
% 1.52/1.73    (![A:$i]:
% 1.52/1.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.52/1.73       ( ![B:$i]:
% 1.52/1.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.52/1.73           ( ( v2_tops_1 @ B @ A ) <=>
% 1.52/1.73             ( ![C:$i]:
% 1.52/1.73               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.52/1.73                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 1.52/1.73                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 1.52/1.73  thf(zf_stmt_0, negated_conjecture,
% 1.52/1.73    (~( ![A:$i]:
% 1.52/1.73        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.52/1.73          ( ![B:$i]:
% 1.52/1.73            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.52/1.73              ( ( v2_tops_1 @ B @ A ) <=>
% 1.52/1.73                ( ![C:$i]:
% 1.52/1.73                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.52/1.73                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 1.52/1.73                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 1.52/1.73    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 1.52/1.73  thf('0', plain,
% 1.52/1.73      (![X30 : $i]:
% 1.52/1.73         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.52/1.73          | ((X30) = (k1_xboole_0))
% 1.52/1.73          | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.52/1.73          | ~ (r1_tarski @ X30 @ sk_B)
% 1.52/1.73          | (v2_tops_1 @ sk_B @ sk_A))),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf('1', plain,
% 1.52/1.73      ((![X30 : $i]:
% 1.52/1.73          (((X30) = (k1_xboole_0))
% 1.52/1.73           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.52/1.73           | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.52/1.73           | ~ (r1_tarski @ X30 @ sk_B))) | 
% 1.52/1.73       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.52/1.73      inference('split', [status(esa)], ['0'])).
% 1.52/1.73  thf('2', plain,
% 1.52/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf(t3_subset, axiom,
% 1.52/1.73    (![A:$i,B:$i]:
% 1.52/1.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.52/1.73  thf('3', plain,
% 1.52/1.73      (![X15 : $i, X16 : $i]:
% 1.52/1.73         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.52/1.73      inference('cnf', [status(esa)], [t3_subset])).
% 1.52/1.73  thf('4', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.52/1.73      inference('sup-', [status(thm)], ['2', '3'])).
% 1.52/1.73  thf('5', plain,
% 1.52/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf(t44_tops_1, axiom,
% 1.52/1.73    (![A:$i]:
% 1.52/1.73     ( ( l1_pre_topc @ A ) =>
% 1.52/1.73       ( ![B:$i]:
% 1.52/1.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.52/1.73           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.52/1.73  thf('6', plain,
% 1.52/1.73      (![X23 : $i, X24 : $i]:
% 1.52/1.73         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.52/1.73          | (r1_tarski @ (k1_tops_1 @ X24 @ X23) @ X23)
% 1.52/1.73          | ~ (l1_pre_topc @ X24))),
% 1.52/1.73      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.52/1.73  thf('7', plain,
% 1.52/1.73      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.52/1.73      inference('sup-', [status(thm)], ['5', '6'])).
% 1.52/1.73  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf('9', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.52/1.73      inference('demod', [status(thm)], ['7', '8'])).
% 1.52/1.73  thf(t1_xboole_1, axiom,
% 1.52/1.73    (![A:$i,B:$i,C:$i]:
% 1.52/1.73     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.52/1.73       ( r1_tarski @ A @ C ) ))).
% 1.52/1.73  thf('10', plain,
% 1.52/1.73      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.52/1.73         (~ (r1_tarski @ X7 @ X8)
% 1.52/1.73          | ~ (r1_tarski @ X8 @ X9)
% 1.52/1.73          | (r1_tarski @ X7 @ X9))),
% 1.52/1.73      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.52/1.73  thf('11', plain,
% 1.52/1.73      (![X0 : $i]:
% 1.52/1.73         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.52/1.73          | ~ (r1_tarski @ sk_B @ X0))),
% 1.52/1.73      inference('sup-', [status(thm)], ['9', '10'])).
% 1.52/1.73  thf('12', plain,
% 1.52/1.73      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.52/1.73      inference('sup-', [status(thm)], ['4', '11'])).
% 1.52/1.73  thf('13', plain,
% 1.52/1.73      (![X15 : $i, X17 : $i]:
% 1.52/1.73         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 1.52/1.73      inference('cnf', [status(esa)], [t3_subset])).
% 1.52/1.73  thf('14', plain,
% 1.52/1.73      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.52/1.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.52/1.73      inference('sup-', [status(thm)], ['12', '13'])).
% 1.52/1.73  thf('15', plain,
% 1.52/1.73      ((![X30 : $i]:
% 1.52/1.73          (((X30) = (k1_xboole_0))
% 1.52/1.73           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.52/1.73           | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.52/1.73           | ~ (r1_tarski @ X30 @ sk_B)))
% 1.52/1.73         <= ((![X30 : $i]:
% 1.52/1.73                (((X30) = (k1_xboole_0))
% 1.52/1.73                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.52/1.73                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.52/1.73                 | ~ (r1_tarski @ X30 @ sk_B))))),
% 1.52/1.73      inference('split', [status(esa)], ['0'])).
% 1.52/1.73  thf('16', plain,
% 1.52/1.73      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.52/1.73         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.52/1.73         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 1.52/1.73         <= ((![X30 : $i]:
% 1.52/1.73                (((X30) = (k1_xboole_0))
% 1.52/1.73                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.52/1.73                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.52/1.73                 | ~ (r1_tarski @ X30 @ sk_B))))),
% 1.52/1.73      inference('sup-', [status(thm)], ['14', '15'])).
% 1.52/1.73  thf('17', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.52/1.73      inference('demod', [status(thm)], ['7', '8'])).
% 1.52/1.73  thf('18', plain,
% 1.52/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf(fc9_tops_1, axiom,
% 1.52/1.73    (![A:$i,B:$i]:
% 1.52/1.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.52/1.73         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.52/1.73       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.52/1.73  thf('19', plain,
% 1.52/1.73      (![X21 : $i, X22 : $i]:
% 1.52/1.73         (~ (l1_pre_topc @ X21)
% 1.52/1.73          | ~ (v2_pre_topc @ X21)
% 1.52/1.73          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.52/1.73          | (v3_pre_topc @ (k1_tops_1 @ X21 @ X22) @ X21))),
% 1.52/1.73      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.52/1.73  thf('20', plain,
% 1.52/1.73      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.52/1.73        | ~ (v2_pre_topc @ sk_A)
% 1.52/1.73        | ~ (l1_pre_topc @ sk_A))),
% 1.52/1.73      inference('sup-', [status(thm)], ['18', '19'])).
% 1.52/1.73  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf('23', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.52/1.73      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.52/1.73  thf('24', plain,
% 1.52/1.73      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.52/1.73         <= ((![X30 : $i]:
% 1.52/1.73                (((X30) = (k1_xboole_0))
% 1.52/1.73                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.52/1.73                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.52/1.73                 | ~ (r1_tarski @ X30 @ sk_B))))),
% 1.52/1.73      inference('demod', [status(thm)], ['16', '17', '23'])).
% 1.52/1.73  thf('25', plain,
% 1.52/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf(t84_tops_1, axiom,
% 1.52/1.73    (![A:$i]:
% 1.52/1.73     ( ( l1_pre_topc @ A ) =>
% 1.52/1.73       ( ![B:$i]:
% 1.52/1.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.52/1.73           ( ( v2_tops_1 @ B @ A ) <=>
% 1.52/1.73             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.52/1.73  thf('26', plain,
% 1.52/1.73      (![X28 : $i, X29 : $i]:
% 1.52/1.73         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.52/1.73          | ((k1_tops_1 @ X29 @ X28) != (k1_xboole_0))
% 1.52/1.73          | (v2_tops_1 @ X28 @ X29)
% 1.52/1.73          | ~ (l1_pre_topc @ X29))),
% 1.52/1.73      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.52/1.73  thf('27', plain,
% 1.52/1.73      ((~ (l1_pre_topc @ sk_A)
% 1.52/1.73        | (v2_tops_1 @ sk_B @ sk_A)
% 1.52/1.73        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 1.52/1.73      inference('sup-', [status(thm)], ['25', '26'])).
% 1.52/1.73  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf('29', plain,
% 1.52/1.73      (((v2_tops_1 @ sk_B @ sk_A)
% 1.52/1.73        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 1.52/1.73      inference('demod', [status(thm)], ['27', '28'])).
% 1.52/1.73  thf('30', plain,
% 1.52/1.73      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 1.52/1.73         <= ((![X30 : $i]:
% 1.52/1.73                (((X30) = (k1_xboole_0))
% 1.52/1.73                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.52/1.73                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.52/1.73                 | ~ (r1_tarski @ X30 @ sk_B))))),
% 1.52/1.73      inference('sup-', [status(thm)], ['24', '29'])).
% 1.52/1.73  thf('31', plain,
% 1.52/1.73      (((v2_tops_1 @ sk_B @ sk_A))
% 1.52/1.73         <= ((![X30 : $i]:
% 1.52/1.73                (((X30) = (k1_xboole_0))
% 1.52/1.73                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.52/1.73                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.52/1.73                 | ~ (r1_tarski @ X30 @ sk_B))))),
% 1.52/1.73      inference('simplify', [status(thm)], ['30'])).
% 1.52/1.73  thf('32', plain,
% 1.52/1.73      (((r1_tarski @ sk_C_1 @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf('33', plain,
% 1.52/1.73      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 1.52/1.73      inference('split', [status(esa)], ['32'])).
% 1.52/1.73  thf('34', plain,
% 1.52/1.73      (~
% 1.52/1.73       (![X30 : $i]:
% 1.52/1.73          (((X30) = (k1_xboole_0))
% 1.52/1.73           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.52/1.73           | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.52/1.73           | ~ (r1_tarski @ X30 @ sk_B))) | 
% 1.52/1.73       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.52/1.73      inference('sup-', [status(thm)], ['31', '33'])).
% 1.52/1.73  thf('35', plain,
% 1.52/1.73      (((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.52/1.73      inference('split', [status(esa)], ['32'])).
% 1.52/1.73  thf('36', plain,
% 1.52/1.73      (((v3_pre_topc @ sk_C_1 @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf('37', plain,
% 1.52/1.73      (((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.52/1.73      inference('split', [status(esa)], ['36'])).
% 1.52/1.73  thf('38', plain,
% 1.52/1.73      ((((sk_C_1) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf('39', plain,
% 1.52/1.73      (~ (((sk_C_1) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.52/1.73      inference('split', [status(esa)], ['38'])).
% 1.52/1.73  thf('40', plain,
% 1.52/1.73      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.52/1.73        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf('41', plain,
% 1.52/1.73      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 1.52/1.73       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.52/1.73      inference('split', [status(esa)], ['40'])).
% 1.52/1.73  thf('42', plain,
% 1.52/1.73      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.52/1.73      inference('split', [status(esa)], ['0'])).
% 1.52/1.73  thf('43', plain,
% 1.52/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf('44', plain,
% 1.52/1.73      (![X28 : $i, X29 : $i]:
% 1.52/1.73         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.52/1.73          | ~ (v2_tops_1 @ X28 @ X29)
% 1.52/1.73          | ((k1_tops_1 @ X29 @ X28) = (k1_xboole_0))
% 1.52/1.73          | ~ (l1_pre_topc @ X29))),
% 1.52/1.73      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.52/1.73  thf('45', plain,
% 1.52/1.73      ((~ (l1_pre_topc @ sk_A)
% 1.52/1.73        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.52/1.73        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.52/1.73      inference('sup-', [status(thm)], ['43', '44'])).
% 1.52/1.73  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf('47', plain,
% 1.52/1.73      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.52/1.73        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.52/1.73      inference('demod', [status(thm)], ['45', '46'])).
% 1.52/1.73  thf('48', plain,
% 1.52/1.73      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.52/1.73         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.52/1.73      inference('sup-', [status(thm)], ['42', '47'])).
% 1.52/1.73  thf('49', plain,
% 1.52/1.73      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 1.52/1.73      inference('split', [status(esa)], ['32'])).
% 1.52/1.73  thf('50', plain,
% 1.52/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf('51', plain,
% 1.52/1.73      (((v3_pre_topc @ sk_C_1 @ sk_A)) <= (((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 1.52/1.73      inference('split', [status(esa)], ['36'])).
% 1.52/1.73  thf('52', plain,
% 1.52/1.73      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.52/1.73         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.73      inference('split', [status(esa)], ['40'])).
% 1.52/1.73  thf(t56_tops_1, axiom,
% 1.52/1.73    (![A:$i]:
% 1.52/1.73     ( ( l1_pre_topc @ A ) =>
% 1.52/1.73       ( ![B:$i]:
% 1.52/1.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.52/1.73           ( ![C:$i]:
% 1.52/1.73             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.52/1.73               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.52/1.73                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.52/1.73  thf('53', plain,
% 1.52/1.73      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.52/1.73         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.52/1.73          | ~ (v3_pre_topc @ X25 @ X26)
% 1.52/1.73          | ~ (r1_tarski @ X25 @ X27)
% 1.52/1.73          | (r1_tarski @ X25 @ (k1_tops_1 @ X26 @ X27))
% 1.52/1.73          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.52/1.73          | ~ (l1_pre_topc @ X26))),
% 1.52/1.73      inference('cnf', [status(esa)], [t56_tops_1])).
% 1.52/1.73  thf('54', plain,
% 1.52/1.73      ((![X0 : $i]:
% 1.52/1.73          (~ (l1_pre_topc @ sk_A)
% 1.52/1.73           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.52/1.73           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 1.52/1.73           | ~ (r1_tarski @ sk_C_1 @ X0)
% 1.52/1.73           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)))
% 1.52/1.73         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.73      inference('sup-', [status(thm)], ['52', '53'])).
% 1.52/1.73  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf('56', plain,
% 1.52/1.73      ((![X0 : $i]:
% 1.52/1.73          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.52/1.73           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 1.52/1.73           | ~ (r1_tarski @ sk_C_1 @ X0)
% 1.52/1.73           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)))
% 1.52/1.73         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.73      inference('demod', [status(thm)], ['54', '55'])).
% 1.52/1.73  thf('57', plain,
% 1.52/1.73      ((![X0 : $i]:
% 1.52/1.73          (~ (r1_tarski @ sk_C_1 @ X0)
% 1.52/1.73           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 1.52/1.73           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.52/1.73         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.52/1.73             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.73      inference('sup-', [status(thm)], ['51', '56'])).
% 1.52/1.73  thf('58', plain,
% 1.52/1.73      ((((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B))
% 1.52/1.73         | ~ (r1_tarski @ sk_C_1 @ sk_B)))
% 1.52/1.73         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.52/1.73             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.73      inference('sup-', [status(thm)], ['50', '57'])).
% 1.52/1.73  thf('59', plain,
% 1.52/1.73      (((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.52/1.73         <= (((r1_tarski @ sk_C_1 @ sk_B)) & 
% 1.52/1.73             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.52/1.73             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.73      inference('sup-', [status(thm)], ['49', '58'])).
% 1.52/1.73  thf('60', plain,
% 1.52/1.73      (((r1_tarski @ sk_C_1 @ k1_xboole_0))
% 1.52/1.73         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 1.52/1.73             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 1.52/1.73             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.52/1.73             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.73      inference('sup+', [status(thm)], ['48', '59'])).
% 1.52/1.73  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 1.52/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.73  thf(d3_tarski, axiom,
% 1.52/1.73    (![A:$i,B:$i]:
% 1.52/1.73     ( ( r1_tarski @ A @ B ) <=>
% 1.52/1.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.52/1.73  thf('62', plain,
% 1.52/1.73      (![X1 : $i, X3 : $i]:
% 1.52/1.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.52/1.73      inference('cnf', [status(esa)], [d3_tarski])).
% 1.52/1.73  thf(dt_k2_subset_1, axiom,
% 1.52/1.73    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.52/1.73  thf('63', plain,
% 1.52/1.73      (![X14 : $i]: (m1_subset_1 @ (k2_subset_1 @ X14) @ (k1_zfmisc_1 @ X14))),
% 1.52/1.73      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.52/1.73  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.52/1.73  thf('64', plain, (![X13 : $i]: ((k2_subset_1 @ X13) = (X13))),
% 1.52/1.73      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.52/1.73  thf('65', plain, (![X14 : $i]: (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X14))),
% 1.52/1.73      inference('demod', [status(thm)], ['63', '64'])).
% 1.52/1.73  thf(t5_subset, axiom,
% 1.52/1.73    (![A:$i,B:$i,C:$i]:
% 1.52/1.73     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.52/1.73          ( v1_xboole_0 @ C ) ) ))).
% 1.52/1.73  thf('66', plain,
% 1.52/1.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.52/1.73         (~ (r2_hidden @ X18 @ X19)
% 1.52/1.73          | ~ (v1_xboole_0 @ X20)
% 1.52/1.73          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.52/1.73      inference('cnf', [status(esa)], [t5_subset])).
% 1.52/1.73  thf('67', plain,
% 1.52/1.73      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.52/1.73      inference('sup-', [status(thm)], ['65', '66'])).
% 1.52/1.73  thf('68', plain,
% 1.52/1.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.52/1.73      inference('sup-', [status(thm)], ['62', '67'])).
% 1.52/1.73  thf('69', plain,
% 1.52/1.73      (![X15 : $i, X17 : $i]:
% 1.52/1.73         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 1.52/1.73      inference('cnf', [status(esa)], [t3_subset])).
% 1.52/1.73  thf('70', plain,
% 1.52/1.73      (![X0 : $i, X1 : $i]:
% 1.52/1.73         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.52/1.73      inference('sup-', [status(thm)], ['68', '69'])).
% 1.52/1.73  thf('71', plain,
% 1.52/1.73      (![X23 : $i, X24 : $i]:
% 1.52/1.73         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.52/1.73          | (r1_tarski @ (k1_tops_1 @ X24 @ X23) @ X23)
% 1.52/1.73          | ~ (l1_pre_topc @ X24))),
% 1.52/1.73      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.52/1.73  thf('72', plain,
% 1.52/1.73      (![X0 : $i, X1 : $i]:
% 1.52/1.73         (~ (v1_xboole_0 @ X1)
% 1.52/1.73          | ~ (l1_pre_topc @ X0)
% 1.52/1.73          | (r1_tarski @ (k1_tops_1 @ X0 @ X1) @ X1))),
% 1.52/1.73      inference('sup-', [status(thm)], ['70', '71'])).
% 1.52/1.73  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.52/1.73  thf('73', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 1.52/1.73      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.52/1.73  thf(t69_xboole_1, axiom,
% 1.52/1.73    (![A:$i,B:$i]:
% 1.52/1.73     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.52/1.73       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 1.52/1.73  thf('74', plain,
% 1.52/1.73      (![X11 : $i, X12 : $i]:
% 1.52/1.73         (~ (r1_xboole_0 @ X11 @ X12)
% 1.52/1.73          | ~ (r1_tarski @ X11 @ X12)
% 1.52/1.73          | (v1_xboole_0 @ X11))),
% 1.52/1.73      inference('cnf', [status(esa)], [t69_xboole_1])).
% 1.52/1.73  thf('75', plain,
% 1.52/1.73      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 1.52/1.73      inference('sup-', [status(thm)], ['73', '74'])).
% 1.52/1.73  thf('76', plain,
% 1.52/1.73      (![X0 : $i]:
% 1.52/1.73         (~ (l1_pre_topc @ X0)
% 1.52/1.73          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.52/1.73          | (v1_xboole_0 @ (k1_tops_1 @ X0 @ k1_xboole_0)))),
% 1.52/1.73      inference('sup-', [status(thm)], ['72', '75'])).
% 1.52/1.73  thf(d10_xboole_0, axiom,
% 1.52/1.73    (![A:$i,B:$i]:
% 1.52/1.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.52/1.73  thf('77', plain,
% 1.52/1.73      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.52/1.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.52/1.73  thf('78', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.52/1.73      inference('simplify', [status(thm)], ['77'])).
% 1.52/1.73  thf('79', plain,
% 1.52/1.73      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 1.52/1.73      inference('sup-', [status(thm)], ['73', '74'])).
% 1.52/1.73  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.52/1.73      inference('sup-', [status(thm)], ['78', '79'])).
% 1.52/1.73  thf('81', plain,
% 1.52/1.73      (![X0 : $i]:
% 1.52/1.73         (~ (l1_pre_topc @ X0) | (v1_xboole_0 @ (k1_tops_1 @ X0 @ k1_xboole_0)))),
% 1.52/1.73      inference('demod', [status(thm)], ['76', '80'])).
% 1.52/1.73  thf('82', plain,
% 1.52/1.73      (![X1 : $i, X3 : $i]:
% 1.52/1.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.52/1.73      inference('cnf', [status(esa)], [d3_tarski])).
% 1.52/1.73  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.52/1.73      inference('sup-', [status(thm)], ['78', '79'])).
% 1.52/1.73  thf('84', plain,
% 1.52/1.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.52/1.73      inference('sup-', [status(thm)], ['62', '67'])).
% 1.52/1.73  thf('85', plain,
% 1.52/1.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.52/1.73      inference('sup-', [status(thm)], ['62', '67'])).
% 1.52/1.73  thf('86', plain,
% 1.52/1.73      (![X4 : $i, X6 : $i]:
% 1.52/1.73         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.52/1.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.52/1.73  thf('87', plain,
% 1.52/1.73      (![X0 : $i, X1 : $i]:
% 1.52/1.73         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.52/1.73      inference('sup-', [status(thm)], ['85', '86'])).
% 1.52/1.73  thf('88', plain,
% 1.52/1.73      (![X0 : $i, X1 : $i]:
% 1.52/1.73         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.52/1.73      inference('sup-', [status(thm)], ['84', '87'])).
% 1.52/1.73  thf('89', plain,
% 1.52/1.73      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 1.52/1.73      inference('sup-', [status(thm)], ['83', '88'])).
% 1.52/1.73  thf('90', plain,
% 1.52/1.73      (![X0 : $i]:
% 1.52/1.73         (~ (l1_pre_topc @ X0) | (v1_xboole_0 @ (k1_tops_1 @ X0 @ k1_xboole_0)))),
% 1.52/1.74      inference('demod', [status(thm)], ['76', '80'])).
% 1.52/1.74  thf('91', plain,
% 1.52/1.74      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['83', '88'])).
% 1.52/1.74  thf('92', plain,
% 1.52/1.74      (![X0 : $i]:
% 1.52/1.74         (~ (l1_pre_topc @ X0)
% 1.52/1.74          | ((k1_xboole_0) = (k1_tops_1 @ X0 @ k1_xboole_0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['90', '91'])).
% 1.52/1.74  thf('93', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         (((k1_xboole_0) = (k1_tops_1 @ X1 @ X0))
% 1.52/1.74          | ~ (v1_xboole_0 @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X1))),
% 1.52/1.74      inference('sup+', [status(thm)], ['89', '92'])).
% 1.52/1.74  thf('94', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         (~ (v1_xboole_0 @ X1)
% 1.52/1.74          | ~ (l1_pre_topc @ X0)
% 1.52/1.74          | (r1_tarski @ (k1_tops_1 @ X0 @ X1) @ X1))),
% 1.52/1.74      inference('sup-', [status(thm)], ['70', '71'])).
% 1.52/1.74  thf('95', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((r1_tarski @ k1_xboole_0 @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | ~ (v1_xboole_0 @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | ~ (v1_xboole_0 @ X0))),
% 1.52/1.74      inference('sup+', [status(thm)], ['93', '94'])).
% 1.52/1.74  thf('96', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         (~ (v1_xboole_0 @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | (r1_tarski @ k1_xboole_0 @ X0))),
% 1.52/1.74      inference('simplify', [status(thm)], ['95'])).
% 1.52/1.74  thf('97', plain,
% 1.52/1.74      (![X15 : $i, X17 : $i]:
% 1.52/1.74         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 1.52/1.74      inference('cnf', [status(esa)], [t3_subset])).
% 1.52/1.74  thf('98', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         (~ (l1_pre_topc @ X1)
% 1.52/1.74          | ~ (v1_xboole_0 @ X0)
% 1.52/1.74          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['96', '97'])).
% 1.52/1.74  thf('99', plain,
% 1.52/1.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.52/1.74         (~ (r2_hidden @ X18 @ X19)
% 1.52/1.74          | ~ (v1_xboole_0 @ X20)
% 1.52/1.74          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.52/1.74      inference('cnf', [status(esa)], [t5_subset])).
% 1.52/1.74  thf('100', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.74         (~ (v1_xboole_0 @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X2)
% 1.52/1.74          | ~ (v1_xboole_0 @ X0)
% 1.52/1.74          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.52/1.74      inference('sup-', [status(thm)], ['98', '99'])).
% 1.52/1.74  thf('101', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.74         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 1.52/1.74          | ~ (l1_pre_topc @ X2)
% 1.52/1.74          | ~ (v1_xboole_0 @ X0))),
% 1.52/1.74      inference('simplify', [status(thm)], ['100'])).
% 1.52/1.74  thf('102', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.74         ((r1_tarski @ k1_xboole_0 @ X0)
% 1.52/1.74          | ~ (v1_xboole_0 @ X1)
% 1.52/1.74          | ~ (l1_pre_topc @ X2))),
% 1.52/1.74      inference('sup-', [status(thm)], ['82', '101'])).
% 1.52/1.74  thf('103', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.74         (~ (l1_pre_topc @ X0)
% 1.52/1.74          | ~ (l1_pre_topc @ X1)
% 1.52/1.74          | (r1_tarski @ k1_xboole_0 @ X2))),
% 1.52/1.74      inference('sup-', [status(thm)], ['81', '102'])).
% 1.52/1.74  thf('104', plain,
% 1.52/1.74      (![X0 : $i, X1 : $i]:
% 1.52/1.74         ((r1_tarski @ k1_xboole_0 @ X0) | ~ (l1_pre_topc @ X1))),
% 1.52/1.74      inference('condensation', [status(thm)], ['103'])).
% 1.52/1.74  thf('105', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.52/1.74      inference('sup-', [status(thm)], ['61', '104'])).
% 1.52/1.74  thf('106', plain,
% 1.52/1.74      (![X4 : $i, X6 : $i]:
% 1.52/1.74         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.52/1.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.52/1.74  thf('107', plain,
% 1.52/1.74      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.52/1.74      inference('sup-', [status(thm)], ['105', '106'])).
% 1.52/1.74  thf('108', plain,
% 1.52/1.74      ((((sk_C_1) = (k1_xboole_0)))
% 1.52/1.74         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 1.52/1.74             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 1.52/1.74             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.52/1.74             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.74      inference('sup-', [status(thm)], ['60', '107'])).
% 1.52/1.74  thf('109', plain,
% 1.52/1.74      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.52/1.74      inference('split', [status(esa)], ['38'])).
% 1.52/1.74  thf('110', plain,
% 1.52/1.74      ((((sk_C_1) != (sk_C_1)))
% 1.52/1.74         <= (~ (((sk_C_1) = (k1_xboole_0))) & 
% 1.52/1.74             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 1.52/1.74             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 1.52/1.74             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.52/1.74             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.52/1.74      inference('sup-', [status(thm)], ['108', '109'])).
% 1.52/1.74  thf('111', plain,
% 1.52/1.74      (~ ((v3_pre_topc @ sk_C_1 @ sk_A)) | 
% 1.52/1.74       ~ ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 1.52/1.74       ~ ((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 1.52/1.74       (((sk_C_1) = (k1_xboole_0)))),
% 1.52/1.74      inference('simplify', [status(thm)], ['110'])).
% 1.52/1.74  thf('112', plain, ($false),
% 1.52/1.74      inference('sat_resolution*', [status(thm)],
% 1.52/1.74                ['1', '34', '35', '37', '39', '41', '111'])).
% 1.52/1.74  
% 1.52/1.74  % SZS output end Refutation
% 1.52/1.74  
% 1.52/1.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
