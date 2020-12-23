%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oIrX9y4XJO

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:17 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 240 expanded)
%              Number of leaves         :   27 (  78 expanded)
%              Depth                    :   21
%              Number of atoms          : 1141 (2912 expanded)
%              Number of equality atoms :   45 ( 104 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
      | ~ ( r1_tarski @ X25 @ sk_B_1 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B_1 ) )
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['7','8'])).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X16 @ X17 ) @ X16 ) ) ),
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
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','17','23'])).

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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k1_tops_1 @ X24 @ X23 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ! [X25: $i] :
        ( ( X25 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X25 @ sk_A )
        | ~ ( r1_tarski @ X25 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ~ ! [X25: $i] :
          ( ( X25 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X25 @ sk_A )
          | ~ ( r1_tarski @ X25 @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('36',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
   <= ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['32'])).

thf('50',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_tarski @ sk_C_1 @ sk_B_1 ) )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B_1 )
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
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_tops_1 @ X1 @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tops_1 @ X1 @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('75',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k1_tops_1 @ X24 @ X23 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ X1 @ X0 )
      | ( ( k1_tops_1 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_tops_1 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X1: $i] :
      ( ( v2_tops_1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('80',plain,(
    ! [X1: $i] :
      ( ( v2_tops_1 @ k1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('82',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tops_1 @ X23 @ X24 )
      | ( ( k1_tops_1 @ X24 @ X23 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v2_tops_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('90',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ ( k1_tops_1 @ X2 @ X1 ) @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( r1_tarski @ ( k1_tops_1 @ X2 @ X1 ) @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','93'])).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['61','97'])).

thf('99',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B_1 )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','100'])).

thf('102',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('103',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( sk_C_1 != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B_1 )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','34','35','37','39','41','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oIrX9y4XJO
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:26:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.32/1.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.32/1.52  % Solved by: fo/fo7.sh
% 1.32/1.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.32/1.52  % done 2648 iterations in 1.059s
% 1.32/1.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.32/1.52  % SZS output start Refutation
% 1.32/1.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.32/1.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.32/1.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.32/1.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.32/1.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.32/1.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.32/1.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.32/1.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.32/1.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.32/1.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.32/1.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.32/1.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.32/1.52  thf(sk_A_type, type, sk_A: $i).
% 1.32/1.52  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 1.32/1.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.32/1.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.32/1.52  thf(t86_tops_1, conjecture,
% 1.32/1.52    (![A:$i]:
% 1.32/1.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.32/1.52       ( ![B:$i]:
% 1.32/1.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.32/1.52           ( ( v2_tops_1 @ B @ A ) <=>
% 1.32/1.52             ( ![C:$i]:
% 1.32/1.52               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.32/1.52                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 1.32/1.52                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 1.32/1.52  thf(zf_stmt_0, negated_conjecture,
% 1.32/1.52    (~( ![A:$i]:
% 1.32/1.52        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.32/1.52          ( ![B:$i]:
% 1.32/1.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.32/1.52              ( ( v2_tops_1 @ B @ A ) <=>
% 1.32/1.52                ( ![C:$i]:
% 1.32/1.52                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.32/1.52                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 1.32/1.52                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 1.32/1.52    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 1.32/1.52  thf('0', plain,
% 1.32/1.52      (![X25 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.32/1.52          | ((X25) = (k1_xboole_0))
% 1.32/1.52          | ~ (v3_pre_topc @ X25 @ sk_A)
% 1.32/1.52          | ~ (r1_tarski @ X25 @ sk_B_1)
% 1.32/1.52          | (v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('1', plain,
% 1.32/1.52      ((![X25 : $i]:
% 1.32/1.52          (((X25) = (k1_xboole_0))
% 1.32/1.52           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.32/1.52           | ~ (v3_pre_topc @ X25 @ sk_A)
% 1.32/1.52           | ~ (r1_tarski @ X25 @ sk_B_1))) | 
% 1.32/1.52       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.32/1.52      inference('split', [status(esa)], ['0'])).
% 1.32/1.52  thf('2', plain,
% 1.32/1.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf(t3_subset, axiom,
% 1.32/1.52    (![A:$i,B:$i]:
% 1.32/1.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.32/1.52  thf('3', plain,
% 1.32/1.52      (![X13 : $i, X14 : $i]:
% 1.32/1.52         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.52  thf('4', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.32/1.52      inference('sup-', [status(thm)], ['2', '3'])).
% 1.32/1.52  thf('5', plain,
% 1.32/1.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf(t44_tops_1, axiom,
% 1.32/1.52    (![A:$i]:
% 1.32/1.52     ( ( l1_pre_topc @ A ) =>
% 1.32/1.52       ( ![B:$i]:
% 1.32/1.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.32/1.52           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.32/1.52  thf('6', plain,
% 1.32/1.52      (![X18 : $i, X19 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.32/1.52          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ X18)
% 1.32/1.52          | ~ (l1_pre_topc @ X19))),
% 1.32/1.52      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.32/1.52  thf('7', plain,
% 1.32/1.52      ((~ (l1_pre_topc @ sk_A)
% 1.32/1.52        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 1.32/1.52      inference('sup-', [status(thm)], ['5', '6'])).
% 1.32/1.52  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('9', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 1.32/1.52      inference('demod', [status(thm)], ['7', '8'])).
% 1.32/1.52  thf(t1_xboole_1, axiom,
% 1.32/1.52    (![A:$i,B:$i,C:$i]:
% 1.32/1.52     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.32/1.52       ( r1_tarski @ A @ C ) ))).
% 1.32/1.52  thf('10', plain,
% 1.32/1.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.32/1.52         (~ (r1_tarski @ X10 @ X11)
% 1.32/1.52          | ~ (r1_tarski @ X11 @ X12)
% 1.32/1.52          | (r1_tarski @ X10 @ X12))),
% 1.32/1.52      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.32/1.52  thf('11', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ X0)
% 1.32/1.52          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['9', '10'])).
% 1.32/1.52  thf('12', plain,
% 1.32/1.52      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.32/1.52      inference('sup-', [status(thm)], ['4', '11'])).
% 1.32/1.52  thf('13', plain,
% 1.32/1.52      (![X13 : $i, X15 : $i]:
% 1.32/1.52         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.52  thf('14', plain,
% 1.32/1.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 1.32/1.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['12', '13'])).
% 1.32/1.52  thf('15', plain,
% 1.32/1.52      ((![X25 : $i]:
% 1.32/1.52          (((X25) = (k1_xboole_0))
% 1.32/1.52           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.32/1.52           | ~ (v3_pre_topc @ X25 @ sk_A)
% 1.32/1.52           | ~ (r1_tarski @ X25 @ sk_B_1)))
% 1.32/1.52         <= ((![X25 : $i]:
% 1.32/1.52                (((X25) = (k1_xboole_0))
% 1.32/1.52                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.32/1.52                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 1.32/1.52                 | ~ (r1_tarski @ X25 @ sk_B_1))))),
% 1.32/1.52      inference('split', [status(esa)], ['0'])).
% 1.32/1.52  thf('16', plain,
% 1.32/1.52      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 1.32/1.52         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 1.32/1.52         | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 1.32/1.52         <= ((![X25 : $i]:
% 1.32/1.52                (((X25) = (k1_xboole_0))
% 1.32/1.52                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.32/1.52                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 1.32/1.52                 | ~ (r1_tarski @ X25 @ sk_B_1))))),
% 1.32/1.52      inference('sup-', [status(thm)], ['14', '15'])).
% 1.32/1.52  thf('17', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 1.32/1.52      inference('demod', [status(thm)], ['7', '8'])).
% 1.32/1.52  thf('18', plain,
% 1.32/1.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf(fc9_tops_1, axiom,
% 1.32/1.52    (![A:$i,B:$i]:
% 1.32/1.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.32/1.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.32/1.52       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.32/1.52  thf('19', plain,
% 1.32/1.52      (![X16 : $i, X17 : $i]:
% 1.32/1.52         (~ (l1_pre_topc @ X16)
% 1.32/1.52          | ~ (v2_pre_topc @ X16)
% 1.32/1.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.32/1.52          | (v3_pre_topc @ (k1_tops_1 @ X16 @ X17) @ X16))),
% 1.32/1.52      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.32/1.52  thf('20', plain,
% 1.32/1.52      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 1.32/1.52        | ~ (v2_pre_topc @ sk_A)
% 1.32/1.52        | ~ (l1_pre_topc @ sk_A))),
% 1.32/1.52      inference('sup-', [status(thm)], ['18', '19'])).
% 1.32/1.52  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('23', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 1.32/1.52      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.32/1.52  thf('24', plain,
% 1.32/1.52      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 1.32/1.52         <= ((![X25 : $i]:
% 1.32/1.52                (((X25) = (k1_xboole_0))
% 1.32/1.52                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.32/1.52                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 1.32/1.52                 | ~ (r1_tarski @ X25 @ sk_B_1))))),
% 1.32/1.52      inference('demod', [status(thm)], ['16', '17', '23'])).
% 1.32/1.52  thf('25', plain,
% 1.32/1.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf(t84_tops_1, axiom,
% 1.32/1.52    (![A:$i]:
% 1.32/1.52     ( ( l1_pre_topc @ A ) =>
% 1.32/1.52       ( ![B:$i]:
% 1.32/1.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.32/1.52           ( ( v2_tops_1 @ B @ A ) <=>
% 1.32/1.52             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.32/1.52  thf('26', plain,
% 1.32/1.52      (![X23 : $i, X24 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.32/1.52          | ((k1_tops_1 @ X24 @ X23) != (k1_xboole_0))
% 1.32/1.52          | (v2_tops_1 @ X23 @ X24)
% 1.32/1.52          | ~ (l1_pre_topc @ X24))),
% 1.32/1.52      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.32/1.52  thf('27', plain,
% 1.32/1.52      ((~ (l1_pre_topc @ sk_A)
% 1.32/1.52        | (v2_tops_1 @ sk_B_1 @ sk_A)
% 1.32/1.52        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['25', '26'])).
% 1.32/1.52  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('29', plain,
% 1.32/1.52      (((v2_tops_1 @ sk_B_1 @ sk_A)
% 1.32/1.52        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 1.32/1.52      inference('demod', [status(thm)], ['27', '28'])).
% 1.32/1.52  thf('30', plain,
% 1.32/1.52      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B_1 @ sk_A)))
% 1.32/1.52         <= ((![X25 : $i]:
% 1.32/1.52                (((X25) = (k1_xboole_0))
% 1.32/1.52                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.32/1.52                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 1.32/1.52                 | ~ (r1_tarski @ X25 @ sk_B_1))))),
% 1.32/1.52      inference('sup-', [status(thm)], ['24', '29'])).
% 1.32/1.52  thf('31', plain,
% 1.32/1.52      (((v2_tops_1 @ sk_B_1 @ sk_A))
% 1.32/1.52         <= ((![X25 : $i]:
% 1.32/1.52                (((X25) = (k1_xboole_0))
% 1.32/1.52                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.32/1.52                 | ~ (v3_pre_topc @ X25 @ sk_A)
% 1.32/1.52                 | ~ (r1_tarski @ X25 @ sk_B_1))))),
% 1.32/1.52      inference('simplify', [status(thm)], ['30'])).
% 1.32/1.52  thf('32', plain,
% 1.32/1.52      (((r1_tarski @ sk_C_1 @ sk_B_1) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('33', plain,
% 1.32/1.52      ((~ (v2_tops_1 @ sk_B_1 @ sk_A)) <= (~ ((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 1.32/1.52      inference('split', [status(esa)], ['32'])).
% 1.32/1.52  thf('34', plain,
% 1.32/1.52      (~
% 1.32/1.52       (![X25 : $i]:
% 1.32/1.52          (((X25) = (k1_xboole_0))
% 1.32/1.52           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.32/1.52           | ~ (v3_pre_topc @ X25 @ sk_A)
% 1.32/1.52           | ~ (r1_tarski @ X25 @ sk_B_1))) | 
% 1.32/1.52       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.32/1.52      inference('sup-', [status(thm)], ['31', '33'])).
% 1.32/1.52  thf('35', plain,
% 1.32/1.52      (((r1_tarski @ sk_C_1 @ sk_B_1)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.32/1.52      inference('split', [status(esa)], ['32'])).
% 1.32/1.52  thf('36', plain,
% 1.32/1.52      (((v3_pre_topc @ sk_C_1 @ sk_A) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('37', plain,
% 1.32/1.52      (((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.32/1.52      inference('split', [status(esa)], ['36'])).
% 1.32/1.52  thf('38', plain,
% 1.32/1.52      ((((sk_C_1) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('39', plain,
% 1.32/1.52      (~ (((sk_C_1) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.32/1.52      inference('split', [status(esa)], ['38'])).
% 1.32/1.52  thf('40', plain,
% 1.32/1.52      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.32/1.52        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('41', plain,
% 1.32/1.52      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 1.32/1.52       ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.32/1.52      inference('split', [status(esa)], ['40'])).
% 1.32/1.52  thf('42', plain,
% 1.32/1.52      (((v2_tops_1 @ sk_B_1 @ sk_A)) <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 1.32/1.52      inference('split', [status(esa)], ['0'])).
% 1.32/1.52  thf('43', plain,
% 1.32/1.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('44', plain,
% 1.32/1.52      (![X23 : $i, X24 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.32/1.52          | ~ (v2_tops_1 @ X23 @ X24)
% 1.32/1.52          | ((k1_tops_1 @ X24 @ X23) = (k1_xboole_0))
% 1.32/1.52          | ~ (l1_pre_topc @ X24))),
% 1.32/1.52      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.32/1.52  thf('45', plain,
% 1.32/1.52      ((~ (l1_pre_topc @ sk_A)
% 1.32/1.52        | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 1.32/1.52        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.32/1.52      inference('sup-', [status(thm)], ['43', '44'])).
% 1.32/1.52  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('47', plain,
% 1.32/1.52      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 1.32/1.52        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.32/1.52      inference('demod', [status(thm)], ['45', '46'])).
% 1.32/1.52  thf('48', plain,
% 1.32/1.52      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 1.32/1.52         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['42', '47'])).
% 1.32/1.52  thf('49', plain,
% 1.32/1.52      (((r1_tarski @ sk_C_1 @ sk_B_1)) <= (((r1_tarski @ sk_C_1 @ sk_B_1)))),
% 1.32/1.52      inference('split', [status(esa)], ['32'])).
% 1.32/1.52  thf('50', plain,
% 1.32/1.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('51', plain,
% 1.32/1.52      (((v3_pre_topc @ sk_C_1 @ sk_A)) <= (((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 1.32/1.52      inference('split', [status(esa)], ['36'])).
% 1.32/1.52  thf('52', plain,
% 1.32/1.52      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.32/1.52         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.32/1.52      inference('split', [status(esa)], ['40'])).
% 1.32/1.52  thf(t56_tops_1, axiom,
% 1.32/1.52    (![A:$i]:
% 1.32/1.52     ( ( l1_pre_topc @ A ) =>
% 1.32/1.52       ( ![B:$i]:
% 1.32/1.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.32/1.52           ( ![C:$i]:
% 1.32/1.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.32/1.52               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.32/1.52                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.32/1.52  thf('53', plain,
% 1.32/1.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.32/1.52          | ~ (v3_pre_topc @ X20 @ X21)
% 1.32/1.52          | ~ (r1_tarski @ X20 @ X22)
% 1.32/1.52          | (r1_tarski @ X20 @ (k1_tops_1 @ X21 @ X22))
% 1.32/1.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.32/1.52          | ~ (l1_pre_topc @ X21))),
% 1.32/1.52      inference('cnf', [status(esa)], [t56_tops_1])).
% 1.32/1.52  thf('54', plain,
% 1.32/1.52      ((![X0 : $i]:
% 1.32/1.52          (~ (l1_pre_topc @ sk_A)
% 1.32/1.52           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.32/1.52           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 1.32/1.52           | ~ (r1_tarski @ sk_C_1 @ X0)
% 1.32/1.52           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)))
% 1.32/1.52         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.32/1.52      inference('sup-', [status(thm)], ['52', '53'])).
% 1.32/1.52  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf('56', plain,
% 1.32/1.52      ((![X0 : $i]:
% 1.32/1.52          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.32/1.52           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 1.32/1.52           | ~ (r1_tarski @ sk_C_1 @ X0)
% 1.32/1.52           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)))
% 1.32/1.52         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.32/1.52      inference('demod', [status(thm)], ['54', '55'])).
% 1.32/1.52  thf('57', plain,
% 1.32/1.52      ((![X0 : $i]:
% 1.32/1.52          (~ (r1_tarski @ sk_C_1 @ X0)
% 1.32/1.52           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 1.32/1.52           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.32/1.52         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.32/1.52             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.32/1.52      inference('sup-', [status(thm)], ['51', '56'])).
% 1.32/1.52  thf('58', plain,
% 1.32/1.52      ((((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 1.32/1.52         | ~ (r1_tarski @ sk_C_1 @ sk_B_1)))
% 1.32/1.52         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.32/1.52             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.32/1.52      inference('sup-', [status(thm)], ['50', '57'])).
% 1.32/1.52  thf('59', plain,
% 1.32/1.52      (((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 1.32/1.52         <= (((r1_tarski @ sk_C_1 @ sk_B_1)) & 
% 1.32/1.52             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.32/1.52             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.32/1.52      inference('sup-', [status(thm)], ['49', '58'])).
% 1.32/1.52  thf('60', plain,
% 1.32/1.52      (((r1_tarski @ sk_C_1 @ k1_xboole_0))
% 1.32/1.52         <= (((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 1.32/1.52             ((r1_tarski @ sk_C_1 @ sk_B_1)) & 
% 1.32/1.52             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.32/1.52             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.32/1.52      inference('sup+', [status(thm)], ['48', '59'])).
% 1.32/1.52  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 1.32/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.52  thf(d3_tarski, axiom,
% 1.32/1.52    (![A:$i,B:$i]:
% 1.32/1.52     ( ( r1_tarski @ A @ B ) <=>
% 1.32/1.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.32/1.52  thf('62', plain,
% 1.32/1.52      (![X4 : $i, X6 : $i]:
% 1.32/1.52         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.32/1.52      inference('cnf', [status(esa)], [d3_tarski])).
% 1.32/1.52  thf(d1_xboole_0, axiom,
% 1.32/1.52    (![A:$i]:
% 1.32/1.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.32/1.52  thf('63', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.32/1.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.32/1.52  thf('64', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['62', '63'])).
% 1.32/1.52  thf('65', plain,
% 1.32/1.52      (![X13 : $i, X15 : $i]:
% 1.32/1.52         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 1.32/1.52      inference('cnf', [status(esa)], [t3_subset])).
% 1.32/1.52  thf('66', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['64', '65'])).
% 1.32/1.52  thf('67', plain,
% 1.32/1.52      (![X18 : $i, X19 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.32/1.52          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ X18)
% 1.32/1.52          | ~ (l1_pre_topc @ X19))),
% 1.32/1.52      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.32/1.52  thf('68', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (v1_xboole_0 @ X1)
% 1.32/1.52          | ~ (l1_pre_topc @ X0)
% 1.32/1.52          | (r1_tarski @ (k1_tops_1 @ X0 @ X1) @ X1))),
% 1.32/1.52      inference('sup-', [status(thm)], ['66', '67'])).
% 1.32/1.52  thf('69', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['62', '63'])).
% 1.32/1.52  thf(d10_xboole_0, axiom,
% 1.32/1.52    (![A:$i,B:$i]:
% 1.32/1.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.32/1.52  thf('70', plain,
% 1.32/1.52      (![X7 : $i, X9 : $i]:
% 1.32/1.52         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.32/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.32/1.52  thf('71', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['69', '70'])).
% 1.32/1.52  thf('72', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (l1_pre_topc @ X1)
% 1.32/1.52          | ~ (v1_xboole_0 @ X0)
% 1.32/1.52          | ((k1_tops_1 @ X1 @ X0) = (X0))
% 1.32/1.52          | ~ (v1_xboole_0 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['68', '71'])).
% 1.32/1.52  thf('73', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (((k1_tops_1 @ X1 @ X0) = (X0))
% 1.32/1.52          | ~ (v1_xboole_0 @ X0)
% 1.32/1.52          | ~ (l1_pre_topc @ X1))),
% 1.32/1.52      inference('simplify', [status(thm)], ['72'])).
% 1.32/1.52  thf('74', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['64', '65'])).
% 1.32/1.52  thf('75', plain,
% 1.32/1.52      (![X23 : $i, X24 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.32/1.52          | ((k1_tops_1 @ X24 @ X23) != (k1_xboole_0))
% 1.32/1.52          | (v2_tops_1 @ X23 @ X24)
% 1.32/1.52          | ~ (l1_pre_topc @ X24))),
% 1.32/1.52      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.32/1.52  thf('76', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (v1_xboole_0 @ X1)
% 1.32/1.52          | ~ (l1_pre_topc @ X0)
% 1.32/1.52          | (v2_tops_1 @ X1 @ X0)
% 1.32/1.52          | ((k1_tops_1 @ X0 @ X1) != (k1_xboole_0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['74', '75'])).
% 1.32/1.52  thf('77', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (((X0) != (k1_xboole_0))
% 1.32/1.52          | ~ (l1_pre_topc @ X1)
% 1.32/1.52          | ~ (v1_xboole_0 @ X0)
% 1.32/1.52          | (v2_tops_1 @ X0 @ X1)
% 1.32/1.52          | ~ (l1_pre_topc @ X1)
% 1.32/1.52          | ~ (v1_xboole_0 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['73', '76'])).
% 1.32/1.52  thf('78', plain,
% 1.32/1.52      (![X1 : $i]:
% 1.32/1.52         ((v2_tops_1 @ k1_xboole_0 @ X1)
% 1.32/1.52          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.32/1.52          | ~ (l1_pre_topc @ X1))),
% 1.32/1.52      inference('simplify', [status(thm)], ['77'])).
% 1.32/1.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.32/1.52  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.32/1.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.32/1.52  thf('80', plain,
% 1.32/1.52      (![X1 : $i]: ((v2_tops_1 @ k1_xboole_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 1.32/1.52      inference('simplify_reflect+', [status(thm)], ['78', '79'])).
% 1.32/1.52  thf('81', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['64', '65'])).
% 1.32/1.52  thf('82', plain,
% 1.32/1.52      (![X23 : $i, X24 : $i]:
% 1.32/1.52         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.32/1.52          | ~ (v2_tops_1 @ X23 @ X24)
% 1.32/1.52          | ((k1_tops_1 @ X24 @ X23) = (k1_xboole_0))
% 1.32/1.52          | ~ (l1_pre_topc @ X24))),
% 1.32/1.52      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.32/1.52  thf('83', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (v1_xboole_0 @ X1)
% 1.32/1.52          | ~ (l1_pre_topc @ X0)
% 1.32/1.52          | ((k1_tops_1 @ X0 @ X1) = (k1_xboole_0))
% 1.32/1.52          | ~ (v2_tops_1 @ X1 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['81', '82'])).
% 1.32/1.52  thf('84', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (~ (l1_pre_topc @ X0)
% 1.32/1.52          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 1.32/1.52          | ~ (l1_pre_topc @ X0)
% 1.32/1.52          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['80', '83'])).
% 1.32/1.52  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.32/1.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.32/1.52  thf('86', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (~ (l1_pre_topc @ X0)
% 1.32/1.52          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 1.32/1.52          | ~ (l1_pre_topc @ X0))),
% 1.32/1.52      inference('demod', [status(thm)], ['84', '85'])).
% 1.32/1.52  thf('87', plain,
% 1.32/1.52      (![X0 : $i]:
% 1.32/1.52         (((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 1.32/1.52          | ~ (l1_pre_topc @ X0))),
% 1.32/1.52      inference('simplify', [status(thm)], ['86'])).
% 1.32/1.52  thf('88', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.32/1.52      inference('sup-', [status(thm)], ['62', '63'])).
% 1.32/1.52  thf('89', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (v1_xboole_0 @ X1)
% 1.32/1.52          | ~ (l1_pre_topc @ X0)
% 1.32/1.52          | (r1_tarski @ (k1_tops_1 @ X0 @ X1) @ X1))),
% 1.32/1.52      inference('sup-', [status(thm)], ['66', '67'])).
% 1.32/1.52  thf('90', plain,
% 1.32/1.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.32/1.52         (~ (r1_tarski @ X10 @ X11)
% 1.32/1.52          | ~ (r1_tarski @ X11 @ X12)
% 1.32/1.52          | (r1_tarski @ X10 @ X12))),
% 1.32/1.52      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.32/1.52  thf('91', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         (~ (l1_pre_topc @ X1)
% 1.32/1.52          | ~ (v1_xboole_0 @ X0)
% 1.32/1.52          | (r1_tarski @ (k1_tops_1 @ X1 @ X0) @ X2)
% 1.32/1.52          | ~ (r1_tarski @ X0 @ X2))),
% 1.32/1.52      inference('sup-', [status(thm)], ['89', '90'])).
% 1.32/1.52  thf('92', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         (~ (v1_xboole_0 @ X1)
% 1.32/1.52          | (r1_tarski @ (k1_tops_1 @ X2 @ X1) @ X0)
% 1.32/1.52          | ~ (v1_xboole_0 @ X1)
% 1.32/1.52          | ~ (l1_pre_topc @ X2))),
% 1.32/1.52      inference('sup-', [status(thm)], ['88', '91'])).
% 1.32/1.52  thf('93', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.52         (~ (l1_pre_topc @ X2)
% 1.32/1.52          | (r1_tarski @ (k1_tops_1 @ X2 @ X1) @ X0)
% 1.32/1.52          | ~ (v1_xboole_0 @ X1))),
% 1.32/1.52      inference('simplify', [status(thm)], ['92'])).
% 1.32/1.52  thf('94', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         ((r1_tarski @ k1_xboole_0 @ X0)
% 1.32/1.52          | ~ (l1_pre_topc @ X1)
% 1.32/1.52          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.32/1.52          | ~ (l1_pre_topc @ X1))),
% 1.32/1.52      inference('sup+', [status(thm)], ['87', '93'])).
% 1.32/1.52  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.32/1.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.32/1.52  thf('96', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         ((r1_tarski @ k1_xboole_0 @ X0)
% 1.32/1.52          | ~ (l1_pre_topc @ X1)
% 1.32/1.52          | ~ (l1_pre_topc @ X1))),
% 1.32/1.52      inference('demod', [status(thm)], ['94', '95'])).
% 1.32/1.52  thf('97', plain,
% 1.32/1.52      (![X0 : $i, X1 : $i]:
% 1.32/1.52         (~ (l1_pre_topc @ X1) | (r1_tarski @ k1_xboole_0 @ X0))),
% 1.32/1.52      inference('simplify', [status(thm)], ['96'])).
% 1.32/1.52  thf('98', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.32/1.52      inference('sup-', [status(thm)], ['61', '97'])).
% 1.32/1.52  thf('99', plain,
% 1.32/1.52      (![X7 : $i, X9 : $i]:
% 1.32/1.52         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.32/1.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.32/1.52  thf('100', plain,
% 1.32/1.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.32/1.52      inference('sup-', [status(thm)], ['98', '99'])).
% 1.32/1.52  thf('101', plain,
% 1.32/1.52      ((((sk_C_1) = (k1_xboole_0)))
% 1.32/1.52         <= (((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 1.32/1.52             ((r1_tarski @ sk_C_1 @ sk_B_1)) & 
% 1.32/1.52             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.32/1.52             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.32/1.52      inference('sup-', [status(thm)], ['60', '100'])).
% 1.32/1.52  thf('102', plain,
% 1.32/1.52      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.32/1.52      inference('split', [status(esa)], ['38'])).
% 1.32/1.52  thf('103', plain,
% 1.32/1.52      ((((sk_C_1) != (sk_C_1)))
% 1.32/1.52         <= (~ (((sk_C_1) = (k1_xboole_0))) & 
% 1.32/1.52             ((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 1.32/1.52             ((r1_tarski @ sk_C_1 @ sk_B_1)) & 
% 1.32/1.52             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 1.32/1.52             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.32/1.52      inference('sup-', [status(thm)], ['101', '102'])).
% 1.32/1.52  thf('104', plain,
% 1.32/1.52      (~ ((v3_pre_topc @ sk_C_1 @ sk_A)) | 
% 1.32/1.52       ~ ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 1.32/1.52       ~ ((r1_tarski @ sk_C_1 @ sk_B_1)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A)) | 
% 1.32/1.52       (((sk_C_1) = (k1_xboole_0)))),
% 1.32/1.52      inference('simplify', [status(thm)], ['103'])).
% 1.32/1.52  thf('105', plain, ($false),
% 1.32/1.52      inference('sat_resolution*', [status(thm)],
% 1.32/1.52                ['1', '34', '35', '37', '39', '41', '104'])).
% 1.32/1.52  
% 1.32/1.52  % SZS output end Refutation
% 1.32/1.52  
% 1.38/1.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
