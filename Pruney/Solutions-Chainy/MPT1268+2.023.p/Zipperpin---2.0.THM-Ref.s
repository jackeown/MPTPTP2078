%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cLCA6ykA3d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:19 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 300 expanded)
%              Number of leaves         :   24 (  91 expanded)
%              Depth                    :   21
%              Number of atoms          : 1305 (4026 expanded)
%              Number of equality atoms :   41 ( 132 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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

thf('0',plain,(
    ! [X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X24 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X24 @ sk_A )
      | ~ ( r1_tarski @ X24 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) )
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
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
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
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X24 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X24 @ sk_A )
      | ~ ( r1_tarski @ X24 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X15 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('21',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k1_tops_1 @ X23 @ X22 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X24: $i] :
        ( ( X24 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X24 @ sk_A )
        | ~ ( r1_tarski @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ~ ! [X24: $i] :
          ( ( X24 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X24 @ sk_A )
          | ~ ( r1_tarski @ X24 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['33'])).

thf('39',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tops_1 @ X22 @ X23 )
      | ( ( k1_tops_1 @ X23 @ X22 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['41'])).

thf('51',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['41'])).

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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( r1_tarski @ X19 @ ( k1_tops_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ sk_C @ sk_C ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['58','60'])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['41'])).

thf('63',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('64',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( sk_C
        = ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('72',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['33'])).

thf('73',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,
    ( ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('77',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X18 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('80',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['75','84'])).

thf('86',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('87',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( r1_tarski @ X19 @ ( k1_tops_1 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 )
        | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('92',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X15 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('93',plain,
    ( ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['89','90','96'])).

thf('98',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['70','97'])).

thf('99',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['33'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('101',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['69','102'])).

thf('104',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['49','103'])).

thf('105',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('106',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('109',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['104','113'])).

thf('115',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('116',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','35','37','38','40','42','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cLCA6ykA3d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.92/1.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.92/1.18  % Solved by: fo/fo7.sh
% 0.92/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.18  % done 3232 iterations in 0.737s
% 0.92/1.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.92/1.18  % SZS output start Refutation
% 0.92/1.18  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.92/1.18  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.92/1.18  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.92/1.18  thf(sk_B_type, type, sk_B: $i).
% 0.92/1.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.92/1.18  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.18  thf(sk_C_type, type, sk_C: $i).
% 0.92/1.18  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.92/1.18  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.92/1.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.92/1.18  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.92/1.18  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.92/1.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.92/1.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.92/1.18  thf(t86_tops_1, conjecture,
% 0.92/1.18    (![A:$i]:
% 0.92/1.18     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.92/1.18       ( ![B:$i]:
% 0.92/1.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.92/1.18           ( ( v2_tops_1 @ B @ A ) <=>
% 0.92/1.18             ( ![C:$i]:
% 0.92/1.18               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.92/1.18                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.92/1.18                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.92/1.18  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.18    (~( ![A:$i]:
% 0.92/1.18        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.92/1.18          ( ![B:$i]:
% 0.92/1.18            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.92/1.18              ( ( v2_tops_1 @ B @ A ) <=>
% 0.92/1.18                ( ![C:$i]:
% 0.92/1.18                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.92/1.18                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.92/1.18                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.92/1.18    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.92/1.18  thf('0', plain,
% 0.92/1.18      (![X24 : $i]:
% 0.92/1.18         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18          | ((X24) = (k1_xboole_0))
% 0.92/1.18          | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.92/1.18          | ~ (r1_tarski @ X24 @ sk_B)
% 0.92/1.18          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('1', plain,
% 0.92/1.18      ((![X24 : $i]:
% 0.92/1.18          (((X24) = (k1_xboole_0))
% 0.92/1.18           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.92/1.18           | ~ (r1_tarski @ X24 @ sk_B))) | 
% 0.92/1.18       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.92/1.18      inference('split', [status(esa)], ['0'])).
% 0.92/1.18  thf('2', plain,
% 0.92/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf(t3_subset, axiom,
% 0.92/1.18    (![A:$i,B:$i]:
% 0.92/1.18     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.92/1.18  thf('3', plain,
% 0.92/1.18      (![X12 : $i, X13 : $i]:
% 0.92/1.18         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.92/1.18      inference('cnf', [status(esa)], [t3_subset])).
% 0.92/1.18  thf('4', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.92/1.18      inference('sup-', [status(thm)], ['2', '3'])).
% 0.92/1.18  thf('5', plain,
% 0.92/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf(t44_tops_1, axiom,
% 0.92/1.18    (![A:$i]:
% 0.92/1.18     ( ( l1_pre_topc @ A ) =>
% 0.92/1.18       ( ![B:$i]:
% 0.92/1.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.92/1.18           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.92/1.18  thf('6', plain,
% 0.92/1.18      (![X17 : $i, X18 : $i]:
% 0.92/1.18         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.92/1.18          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ X17)
% 0.92/1.18          | ~ (l1_pre_topc @ X18))),
% 0.92/1.18      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.92/1.18  thf('7', plain,
% 0.92/1.18      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.92/1.18      inference('sup-', [status(thm)], ['5', '6'])).
% 0.92/1.18  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('9', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.92/1.18      inference('demod', [status(thm)], ['7', '8'])).
% 0.92/1.18  thf(t1_xboole_1, axiom,
% 0.92/1.18    (![A:$i,B:$i,C:$i]:
% 0.92/1.18     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.92/1.18       ( r1_tarski @ A @ C ) ))).
% 0.92/1.18  thf('10', plain,
% 0.92/1.18      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.92/1.18         (~ (r1_tarski @ X9 @ X10)
% 0.92/1.18          | ~ (r1_tarski @ X10 @ X11)
% 0.92/1.18          | (r1_tarski @ X9 @ X11))),
% 0.92/1.18      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.92/1.18  thf('11', plain,
% 0.92/1.18      (![X0 : $i]:
% 0.92/1.18         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.92/1.18          | ~ (r1_tarski @ sk_B @ X0))),
% 0.92/1.18      inference('sup-', [status(thm)], ['9', '10'])).
% 0.92/1.18  thf('12', plain,
% 0.92/1.18      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.92/1.18      inference('sup-', [status(thm)], ['4', '11'])).
% 0.92/1.18  thf('13', plain,
% 0.92/1.18      (![X12 : $i, X14 : $i]:
% 0.92/1.18         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.92/1.18      inference('cnf', [status(esa)], [t3_subset])).
% 0.92/1.18  thf('14', plain,
% 0.92/1.18      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.92/1.18        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['12', '13'])).
% 0.92/1.18  thf('15', plain,
% 0.92/1.18      (![X24 : $i]:
% 0.92/1.18         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18          | ((X24) = (k1_xboole_0))
% 0.92/1.18          | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.92/1.18          | ~ (r1_tarski @ X24 @ sk_B)
% 0.92/1.18          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('16', plain,
% 0.92/1.18      ((![X24 : $i]:
% 0.92/1.18          (((X24) = (k1_xboole_0))
% 0.92/1.18           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.92/1.18           | ~ (r1_tarski @ X24 @ sk_B)))
% 0.92/1.18         <= ((![X24 : $i]:
% 0.92/1.18                (((X24) = (k1_xboole_0))
% 0.92/1.18                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.92/1.18                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.92/1.18      inference('split', [status(esa)], ['15'])).
% 0.92/1.18  thf('17', plain,
% 0.92/1.18      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.92/1.18         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.92/1.18         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.92/1.18         <= ((![X24 : $i]:
% 0.92/1.18                (((X24) = (k1_xboole_0))
% 0.92/1.18                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.92/1.18                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.92/1.18      inference('sup-', [status(thm)], ['14', '16'])).
% 0.92/1.18  thf('18', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.92/1.18      inference('demod', [status(thm)], ['7', '8'])).
% 0.92/1.18  thf('19', plain,
% 0.92/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf(fc9_tops_1, axiom,
% 0.92/1.18    (![A:$i,B:$i]:
% 0.92/1.18     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.92/1.18         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.92/1.18       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.92/1.18  thf('20', plain,
% 0.92/1.18      (![X15 : $i, X16 : $i]:
% 0.92/1.18         (~ (l1_pre_topc @ X15)
% 0.92/1.18          | ~ (v2_pre_topc @ X15)
% 0.92/1.18          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.92/1.18          | (v3_pre_topc @ (k1_tops_1 @ X15 @ X16) @ X15))),
% 0.92/1.18      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.92/1.18  thf('21', plain,
% 0.92/1.18      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.92/1.18        | ~ (v2_pre_topc @ sk_A)
% 0.92/1.18        | ~ (l1_pre_topc @ sk_A))),
% 0.92/1.18      inference('sup-', [status(thm)], ['19', '20'])).
% 0.92/1.18  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('24', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.92/1.18      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.92/1.18  thf('25', plain,
% 0.92/1.18      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.92/1.18         <= ((![X24 : $i]:
% 0.92/1.18                (((X24) = (k1_xboole_0))
% 0.92/1.18                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.92/1.18                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.92/1.18      inference('demod', [status(thm)], ['17', '18', '24'])).
% 0.92/1.18  thf('26', plain,
% 0.92/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf(t84_tops_1, axiom,
% 0.92/1.18    (![A:$i]:
% 0.92/1.18     ( ( l1_pre_topc @ A ) =>
% 0.92/1.18       ( ![B:$i]:
% 0.92/1.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.92/1.18           ( ( v2_tops_1 @ B @ A ) <=>
% 0.92/1.18             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.92/1.18  thf('27', plain,
% 0.92/1.18      (![X22 : $i, X23 : $i]:
% 0.92/1.18         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.92/1.18          | ((k1_tops_1 @ X23 @ X22) != (k1_xboole_0))
% 0.92/1.18          | (v2_tops_1 @ X22 @ X23)
% 0.92/1.18          | ~ (l1_pre_topc @ X23))),
% 0.92/1.18      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.92/1.18  thf('28', plain,
% 0.92/1.18      ((~ (l1_pre_topc @ sk_A)
% 0.92/1.18        | (v2_tops_1 @ sk_B @ sk_A)
% 0.92/1.18        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['26', '27'])).
% 0.92/1.18  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('30', plain,
% 0.92/1.18      (((v2_tops_1 @ sk_B @ sk_A)
% 0.92/1.18        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.92/1.18      inference('demod', [status(thm)], ['28', '29'])).
% 0.92/1.18  thf('31', plain,
% 0.92/1.18      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.92/1.18         <= ((![X24 : $i]:
% 0.92/1.18                (((X24) = (k1_xboole_0))
% 0.92/1.18                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.92/1.18                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.92/1.18      inference('sup-', [status(thm)], ['25', '30'])).
% 0.92/1.18  thf('32', plain,
% 0.92/1.18      (((v2_tops_1 @ sk_B @ sk_A))
% 0.92/1.18         <= ((![X24 : $i]:
% 0.92/1.18                (((X24) = (k1_xboole_0))
% 0.92/1.18                 | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18                 | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.92/1.18                 | ~ (r1_tarski @ X24 @ sk_B))))),
% 0.92/1.18      inference('simplify', [status(thm)], ['31'])).
% 0.92/1.18  thf('33', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('34', plain,
% 0.92/1.18      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.92/1.18      inference('split', [status(esa)], ['33'])).
% 0.92/1.18  thf('35', plain,
% 0.92/1.18      (~
% 0.92/1.18       (![X24 : $i]:
% 0.92/1.18          (((X24) = (k1_xboole_0))
% 0.92/1.18           | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18           | ~ (v3_pre_topc @ X24 @ sk_A)
% 0.92/1.18           | ~ (r1_tarski @ X24 @ sk_B))) | 
% 0.92/1.18       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.92/1.18      inference('sup-', [status(thm)], ['32', '34'])).
% 0.92/1.18  thf('36', plain,
% 0.92/1.18      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('37', plain,
% 0.92/1.18      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.92/1.18      inference('split', [status(esa)], ['36'])).
% 0.92/1.18  thf('38', plain,
% 0.92/1.18      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.92/1.18      inference('split', [status(esa)], ['33'])).
% 0.92/1.18  thf('39', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('40', plain,
% 0.92/1.18      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.92/1.18      inference('split', [status(esa)], ['39'])).
% 0.92/1.18  thf('41', plain,
% 0.92/1.18      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('42', plain,
% 0.92/1.18      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.92/1.18       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.92/1.18      inference('split', [status(esa)], ['41'])).
% 0.92/1.18  thf('43', plain,
% 0.92/1.18      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.92/1.18      inference('split', [status(esa)], ['0'])).
% 0.92/1.18  thf('44', plain,
% 0.92/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('45', plain,
% 0.92/1.18      (![X22 : $i, X23 : $i]:
% 0.92/1.18         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.92/1.18          | ~ (v2_tops_1 @ X22 @ X23)
% 0.92/1.18          | ((k1_tops_1 @ X23 @ X22) = (k1_xboole_0))
% 0.92/1.18          | ~ (l1_pre_topc @ X23))),
% 0.92/1.18      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.92/1.18  thf('46', plain,
% 0.92/1.18      ((~ (l1_pre_topc @ sk_A)
% 0.92/1.18        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.92/1.18        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.92/1.18      inference('sup-', [status(thm)], ['44', '45'])).
% 0.92/1.18  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('48', plain,
% 0.92/1.18      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.92/1.18        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.92/1.18      inference('demod', [status(thm)], ['46', '47'])).
% 0.92/1.18  thf('49', plain,
% 0.92/1.18      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.92/1.18         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['43', '48'])).
% 0.92/1.18  thf('50', plain,
% 0.92/1.18      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.92/1.18         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('split', [status(esa)], ['41'])).
% 0.92/1.18  thf('51', plain,
% 0.92/1.18      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.92/1.18      inference('split', [status(esa)], ['36'])).
% 0.92/1.18  thf('52', plain,
% 0.92/1.18      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.92/1.18         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('split', [status(esa)], ['41'])).
% 0.92/1.18  thf(t56_tops_1, axiom,
% 0.92/1.18    (![A:$i]:
% 0.92/1.18     ( ( l1_pre_topc @ A ) =>
% 0.92/1.18       ( ![B:$i]:
% 0.92/1.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.92/1.18           ( ![C:$i]:
% 0.92/1.18             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.92/1.18               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.92/1.18                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.92/1.18  thf('53', plain,
% 0.92/1.18      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.92/1.18         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.92/1.18          | ~ (v3_pre_topc @ X19 @ X20)
% 0.92/1.18          | ~ (r1_tarski @ X19 @ X21)
% 0.92/1.18          | (r1_tarski @ X19 @ (k1_tops_1 @ X20 @ X21))
% 0.92/1.18          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.92/1.18          | ~ (l1_pre_topc @ X20))),
% 0.92/1.18      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.92/1.18  thf('54', plain,
% 0.92/1.18      ((![X0 : $i]:
% 0.92/1.18          (~ (l1_pre_topc @ sk_A)
% 0.92/1.18           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.92/1.18           | ~ (r1_tarski @ sk_C @ X0)
% 0.92/1.18           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.92/1.18         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('sup-', [status(thm)], ['52', '53'])).
% 0.92/1.18  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('56', plain,
% 0.92/1.18      ((![X0 : $i]:
% 0.92/1.18          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.92/1.18           | ~ (r1_tarski @ sk_C @ X0)
% 0.92/1.18           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.92/1.18         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('demod', [status(thm)], ['54', '55'])).
% 0.92/1.18  thf('57', plain,
% 0.92/1.18      ((![X0 : $i]:
% 0.92/1.18          (~ (r1_tarski @ sk_C @ X0)
% 0.92/1.18           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.92/1.18           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.92/1.18         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.92/1.18             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('sup-', [status(thm)], ['51', '56'])).
% 0.92/1.18  thf('58', plain,
% 0.92/1.18      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_C))
% 0.92/1.18         | ~ (r1_tarski @ sk_C @ sk_C)))
% 0.92/1.18         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.92/1.18             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('sup-', [status(thm)], ['50', '57'])).
% 0.92/1.18  thf(d10_xboole_0, axiom,
% 0.92/1.18    (![A:$i,B:$i]:
% 0.92/1.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.92/1.18  thf('59', plain,
% 0.92/1.18      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.92/1.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.92/1.18  thf('60', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.92/1.18      inference('simplify', [status(thm)], ['59'])).
% 0.92/1.18  thf('61', plain,
% 0.92/1.18      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.92/1.18         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.92/1.18             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('demod', [status(thm)], ['58', '60'])).
% 0.92/1.18  thf('62', plain,
% 0.92/1.18      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.92/1.18         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('split', [status(esa)], ['41'])).
% 0.92/1.18  thf('63', plain,
% 0.92/1.18      (![X17 : $i, X18 : $i]:
% 0.92/1.18         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.92/1.18          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ X17)
% 0.92/1.18          | ~ (l1_pre_topc @ X18))),
% 0.92/1.18      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.92/1.18  thf('64', plain,
% 0.92/1.18      (((~ (l1_pre_topc @ sk_A)
% 0.92/1.18         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)))
% 0.92/1.18         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('sup-', [status(thm)], ['62', '63'])).
% 0.92/1.18  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('66', plain,
% 0.92/1.18      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))
% 0.92/1.18         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('demod', [status(thm)], ['64', '65'])).
% 0.92/1.18  thf('67', plain,
% 0.92/1.18      (![X0 : $i, X2 : $i]:
% 0.92/1.18         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.92/1.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.92/1.18  thf('68', plain,
% 0.92/1.18      (((~ (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_C))
% 0.92/1.18         | ((sk_C) = (k1_tops_1 @ sk_A @ sk_C))))
% 0.92/1.18         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('sup-', [status(thm)], ['66', '67'])).
% 0.92/1.18  thf('69', plain,
% 0.92/1.18      ((((sk_C) = (k1_tops_1 @ sk_A @ sk_C)))
% 0.92/1.18         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.92/1.18             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('sup-', [status(thm)], ['61', '68'])).
% 0.92/1.18  thf('70', plain,
% 0.92/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('71', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.92/1.18      inference('sup-', [status(thm)], ['2', '3'])).
% 0.92/1.18  thf('72', plain,
% 0.92/1.18      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('split', [status(esa)], ['33'])).
% 0.92/1.18  thf('73', plain,
% 0.92/1.18      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.92/1.18         (~ (r1_tarski @ X9 @ X10)
% 0.92/1.18          | ~ (r1_tarski @ X10 @ X11)
% 0.92/1.18          | (r1_tarski @ X9 @ X11))),
% 0.92/1.18      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.92/1.18  thf('74', plain,
% 0.92/1.18      ((![X0 : $i]: ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ sk_B @ X0)))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['72', '73'])).
% 0.92/1.18  thf('75', plain,
% 0.92/1.18      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['71', '74'])).
% 0.92/1.18  thf('76', plain,
% 0.92/1.18      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['71', '74'])).
% 0.92/1.18  thf('77', plain,
% 0.92/1.18      (![X12 : $i, X14 : $i]:
% 0.92/1.18         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.92/1.18      inference('cnf', [status(esa)], [t3_subset])).
% 0.92/1.18  thf('78', plain,
% 0.92/1.18      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['76', '77'])).
% 0.92/1.18  thf('79', plain,
% 0.92/1.18      (![X17 : $i, X18 : $i]:
% 0.92/1.18         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.92/1.18          | (r1_tarski @ (k1_tops_1 @ X18 @ X17) @ X17)
% 0.92/1.18          | ~ (l1_pre_topc @ X18))),
% 0.92/1.18      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.92/1.18  thf('80', plain,
% 0.92/1.18      (((~ (l1_pre_topc @ sk_A)
% 0.92/1.18         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['78', '79'])).
% 0.92/1.18  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('82', plain,
% 0.92/1.18      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('demod', [status(thm)], ['80', '81'])).
% 0.92/1.18  thf('83', plain,
% 0.92/1.18      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.92/1.18         (~ (r1_tarski @ X9 @ X10)
% 0.92/1.18          | ~ (r1_tarski @ X10 @ X11)
% 0.92/1.18          | (r1_tarski @ X9 @ X11))),
% 0.92/1.18      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.92/1.18  thf('84', plain,
% 0.92/1.18      ((![X0 : $i]:
% 0.92/1.18          ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0)
% 0.92/1.18           | ~ (r1_tarski @ sk_C @ X0)))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['82', '83'])).
% 0.92/1.18  thf('85', plain,
% 0.92/1.18      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['75', '84'])).
% 0.92/1.18  thf('86', plain,
% 0.92/1.18      (![X12 : $i, X14 : $i]:
% 0.92/1.18         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.92/1.18      inference('cnf', [status(esa)], [t3_subset])).
% 0.92/1.18  thf('87', plain,
% 0.92/1.18      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.92/1.18         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['85', '86'])).
% 0.92/1.18  thf('88', plain,
% 0.92/1.18      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.92/1.18         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.92/1.18          | ~ (v3_pre_topc @ X19 @ X20)
% 0.92/1.18          | ~ (r1_tarski @ X19 @ X21)
% 0.92/1.18          | (r1_tarski @ X19 @ (k1_tops_1 @ X20 @ X21))
% 0.92/1.18          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.92/1.18          | ~ (l1_pre_topc @ X20))),
% 0.92/1.18      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.92/1.18  thf('89', plain,
% 0.92/1.18      ((![X0 : $i]:
% 0.92/1.18          (~ (l1_pre_topc @ sk_A)
% 0.92/1.18           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.92/1.18           | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0)
% 0.92/1.18           | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['87', '88'])).
% 0.92/1.18  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('91', plain,
% 0.92/1.18      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['76', '77'])).
% 0.92/1.18  thf('92', plain,
% 0.92/1.18      (![X15 : $i, X16 : $i]:
% 0.92/1.18         (~ (l1_pre_topc @ X15)
% 0.92/1.18          | ~ (v2_pre_topc @ X15)
% 0.92/1.18          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.92/1.18          | (v3_pre_topc @ (k1_tops_1 @ X15 @ X16) @ X15))),
% 0.92/1.18      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.92/1.18  thf('93', plain,
% 0.92/1.18      ((((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.92/1.18         | ~ (v2_pre_topc @ sk_A)
% 0.92/1.18         | ~ (l1_pre_topc @ sk_A))) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['91', '92'])).
% 0.92/1.18  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.92/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.18  thf('96', plain,
% 0.92/1.18      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.92/1.18  thf('97', plain,
% 0.92/1.18      ((![X0 : $i]:
% 0.92/1.18          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.92/1.18           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.92/1.18           | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0)))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('demod', [status(thm)], ['89', '90', '96'])).
% 0.92/1.18  thf('98', plain,
% 0.92/1.18      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_B)
% 0.92/1.18         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['70', '97'])).
% 0.92/1.18  thf('99', plain,
% 0.92/1.18      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('split', [status(esa)], ['33'])).
% 0.92/1.18  thf('100', plain,
% 0.92/1.18      ((![X0 : $i]:
% 0.92/1.18          ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0)
% 0.92/1.18           | ~ (r1_tarski @ sk_C @ X0)))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['82', '83'])).
% 0.92/1.18  thf('101', plain,
% 0.92/1.18      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_B))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['99', '100'])).
% 0.92/1.18  thf('102', plain,
% 0.92/1.18      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.92/1.18      inference('demod', [status(thm)], ['98', '101'])).
% 0.92/1.18  thf('103', plain,
% 0.92/1.18      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.92/1.18         <= (((r1_tarski @ sk_C @ sk_B)) & 
% 0.92/1.18             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.92/1.18             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('sup+', [status(thm)], ['69', '102'])).
% 0.92/1.18  thf('104', plain,
% 0.92/1.18      (((r1_tarski @ sk_C @ k1_xboole_0))
% 0.92/1.18         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.92/1.18             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.92/1.18             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.92/1.18             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('sup+', [status(thm)], ['49', '103'])).
% 0.92/1.18  thf('105', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.92/1.18      inference('simplify', [status(thm)], ['59'])).
% 0.92/1.18  thf(l32_xboole_1, axiom,
% 0.92/1.18    (![A:$i,B:$i]:
% 0.92/1.18     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.92/1.18  thf('106', plain,
% 0.92/1.18      (![X3 : $i, X5 : $i]:
% 0.92/1.18         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.92/1.18      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.92/1.18  thf('107', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.92/1.18      inference('sup-', [status(thm)], ['105', '106'])).
% 0.92/1.18  thf('108', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.92/1.18      inference('simplify', [status(thm)], ['59'])).
% 0.92/1.18  thf(t109_xboole_1, axiom,
% 0.92/1.18    (![A:$i,B:$i,C:$i]:
% 0.92/1.18     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.92/1.18  thf('109', plain,
% 0.92/1.18      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.92/1.18         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k4_xboole_0 @ X6 @ X8) @ X7))),
% 0.92/1.18      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.92/1.18  thf('110', plain,
% 0.92/1.18      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.92/1.18      inference('sup-', [status(thm)], ['108', '109'])).
% 0.92/1.18  thf('111', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.92/1.18      inference('sup+', [status(thm)], ['107', '110'])).
% 0.92/1.18  thf('112', plain,
% 0.92/1.18      (![X0 : $i, X2 : $i]:
% 0.92/1.18         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.92/1.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.92/1.18  thf('113', plain,
% 0.92/1.18      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.92/1.18      inference('sup-', [status(thm)], ['111', '112'])).
% 0.92/1.18  thf('114', plain,
% 0.92/1.18      ((((sk_C) = (k1_xboole_0)))
% 0.92/1.18         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.92/1.18             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.92/1.18             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.92/1.18             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('sup-', [status(thm)], ['104', '113'])).
% 0.92/1.18  thf('115', plain,
% 0.92/1.18      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.92/1.18      inference('split', [status(esa)], ['39'])).
% 0.92/1.18  thf('116', plain,
% 0.92/1.18      ((((sk_C) != (sk_C)))
% 0.92/1.18         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.92/1.18             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.92/1.18             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.92/1.18             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.92/1.18             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.92/1.18      inference('sup-', [status(thm)], ['114', '115'])).
% 0.92/1.18  thf('117', plain,
% 0.92/1.18      (~ ((r1_tarski @ sk_C @ sk_B)) | 
% 0.92/1.18       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.92/1.18       ~ ((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.92/1.18       (((sk_C) = (k1_xboole_0)))),
% 0.92/1.18      inference('simplify', [status(thm)], ['116'])).
% 0.92/1.18  thf('118', plain, ($false),
% 0.92/1.18      inference('sat_resolution*', [status(thm)],
% 0.92/1.18                ['1', '35', '37', '38', '40', '42', '117'])).
% 0.92/1.18  
% 0.92/1.18  % SZS output end Refutation
% 0.92/1.18  
% 1.02/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
