%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AEZj9CL0Ml

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:20 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 160 expanded)
%              Number of leaves         :   24 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  852 (2278 expanded)
%              Number of equality atoms :   36 (  90 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X21: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X21 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X21 @ sk_A )
      | ~ ( r1_tarski @ X21 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) )
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
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X15 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X12 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('22',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19','25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k1_tops_1 @ X20 @ X19 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X21: $i] :
        ( ( X21 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X21 @ sk_A )
        | ~ ( r1_tarski @ X21 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ~ ! [X21: $i] :
          ( ( X21 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X21 @ sk_A )
          | ~ ( r1_tarski @ X21 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['34'])).

thf('38',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tops_1 @ X19 @ X20 )
      | ( ( k1_tops_1 @ X20 @ X19 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['34'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['42'])).

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

thf('55',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ X18 )
      | ( r1_tarski @ X16 @ ( k1_tops_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_C @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['50','61'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('63',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['40'])).

thf('68',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','39','41','43','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AEZj9CL0Ml
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:58:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.62/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.84  % Solved by: fo/fo7.sh
% 0.62/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.84  % done 1109 iterations in 0.389s
% 0.62/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.84  % SZS output start Refutation
% 0.62/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.84  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.62/0.84  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.62/0.84  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.62/0.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.62/0.84  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.62/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.84  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.62/0.84  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.62/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.62/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.62/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.62/0.84  thf(t86_tops_1, conjecture,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.62/0.84       ( ![B:$i]:
% 0.62/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.84           ( ( v2_tops_1 @ B @ A ) <=>
% 0.62/0.84             ( ![C:$i]:
% 0.62/0.84               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.84                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.62/0.84                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.62/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.84    (~( ![A:$i]:
% 0.62/0.84        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.62/0.84          ( ![B:$i]:
% 0.62/0.84            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.84              ( ( v2_tops_1 @ B @ A ) <=>
% 0.62/0.84                ( ![C:$i]:
% 0.62/0.84                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.84                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.62/0.84                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.62/0.84    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.62/0.84  thf('0', plain,
% 0.62/0.84      (![X21 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.84          | ((X21) = (k1_xboole_0))
% 0.62/0.84          | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.62/0.84          | ~ (r1_tarski @ X21 @ sk_B)
% 0.62/0.84          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('1', plain,
% 0.62/0.84      ((![X21 : $i]:
% 0.62/0.84          (((X21) = (k1_xboole_0))
% 0.62/0.84           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.84           | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.62/0.84           | ~ (r1_tarski @ X21 @ sk_B))) | 
% 0.62/0.84       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.62/0.84      inference('split', [status(esa)], ['0'])).
% 0.62/0.84  thf('2', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(t3_subset, axiom,
% 0.62/0.84    (![A:$i,B:$i]:
% 0.62/0.84     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.62/0.84  thf('3', plain,
% 0.62/0.84      (![X9 : $i, X10 : $i]:
% 0.62/0.84         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.62/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.62/0.84  thf('4', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['2', '3'])).
% 0.62/0.84  thf('5', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(t44_tops_1, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( l1_pre_topc @ A ) =>
% 0.62/0.84       ( ![B:$i]:
% 0.62/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.84           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.62/0.84  thf('6', plain,
% 0.62/0.84      (![X14 : $i, X15 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.62/0.84          | (r1_tarski @ (k1_tops_1 @ X15 @ X14) @ X14)
% 0.62/0.84          | ~ (l1_pre_topc @ X15))),
% 0.62/0.84      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.62/0.84  thf('7', plain,
% 0.62/0.84      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.62/0.84      inference('sup-', [status(thm)], ['5', '6'])).
% 0.62/0.84  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('9', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.62/0.84      inference('demod', [status(thm)], ['7', '8'])).
% 0.62/0.84  thf(t12_xboole_1, axiom,
% 0.62/0.84    (![A:$i,B:$i]:
% 0.62/0.84     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.62/0.84  thf('10', plain,
% 0.62/0.84      (![X6 : $i, X7 : $i]:
% 0.62/0.84         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.62/0.84      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.62/0.84  thf('11', plain,
% 0.62/0.84      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 0.62/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.62/0.84  thf(t11_xboole_1, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.62/0.84  thf('12', plain,
% 0.62/0.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.62/0.84         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.62/0.84      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.62/0.84  thf('13', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         (~ (r1_tarski @ sk_B @ X0)
% 0.62/0.84          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['11', '12'])).
% 0.62/0.84  thf('14', plain,
% 0.62/0.84      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['4', '13'])).
% 0.62/0.84  thf('15', plain,
% 0.62/0.84      (![X9 : $i, X11 : $i]:
% 0.62/0.84         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.62/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.62/0.84  thf('16', plain,
% 0.62/0.84      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.62/0.84        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['14', '15'])).
% 0.62/0.84  thf('17', plain,
% 0.62/0.84      ((![X21 : $i]:
% 0.62/0.84          (((X21) = (k1_xboole_0))
% 0.62/0.84           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.84           | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.62/0.84           | ~ (r1_tarski @ X21 @ sk_B)))
% 0.62/0.84         <= ((![X21 : $i]:
% 0.62/0.84                (((X21) = (k1_xboole_0))
% 0.62/0.84                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.84                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.62/0.84                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.62/0.84      inference('split', [status(esa)], ['0'])).
% 0.62/0.84  thf('18', plain,
% 0.62/0.84      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.62/0.84         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.62/0.84         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.62/0.84         <= ((![X21 : $i]:
% 0.62/0.84                (((X21) = (k1_xboole_0))
% 0.62/0.84                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.84                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.62/0.84                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['16', '17'])).
% 0.62/0.84  thf('19', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.62/0.84      inference('demod', [status(thm)], ['7', '8'])).
% 0.62/0.84  thf('20', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(fc9_tops_1, axiom,
% 0.62/0.84    (![A:$i,B:$i]:
% 0.62/0.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.62/0.84         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.62/0.84       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.62/0.84  thf('21', plain,
% 0.62/0.84      (![X12 : $i, X13 : $i]:
% 0.62/0.84         (~ (l1_pre_topc @ X12)
% 0.62/0.84          | ~ (v2_pre_topc @ X12)
% 0.62/0.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.62/0.84          | (v3_pre_topc @ (k1_tops_1 @ X12 @ X13) @ X12))),
% 0.62/0.84      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.62/0.84  thf('22', plain,
% 0.62/0.84      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.62/0.84        | ~ (v2_pre_topc @ sk_A)
% 0.62/0.84        | ~ (l1_pre_topc @ sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['20', '21'])).
% 0.62/0.84  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('25', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.62/0.84      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.62/0.84  thf('26', plain,
% 0.62/0.84      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.62/0.84         <= ((![X21 : $i]:
% 0.62/0.84                (((X21) = (k1_xboole_0))
% 0.62/0.84                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.84                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.62/0.84                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.62/0.84      inference('demod', [status(thm)], ['18', '19', '25'])).
% 0.62/0.84  thf('27', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(t84_tops_1, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( l1_pre_topc @ A ) =>
% 0.62/0.84       ( ![B:$i]:
% 0.62/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.84           ( ( v2_tops_1 @ B @ A ) <=>
% 0.62/0.84             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.62/0.84  thf('28', plain,
% 0.62/0.84      (![X19 : $i, X20 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.62/0.84          | ((k1_tops_1 @ X20 @ X19) != (k1_xboole_0))
% 0.62/0.84          | (v2_tops_1 @ X19 @ X20)
% 0.62/0.84          | ~ (l1_pre_topc @ X20))),
% 0.62/0.84      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.62/0.84  thf('29', plain,
% 0.62/0.84      ((~ (l1_pre_topc @ sk_A)
% 0.62/0.84        | (v2_tops_1 @ sk_B @ sk_A)
% 0.62/0.84        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['27', '28'])).
% 0.62/0.84  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('31', plain,
% 0.62/0.84      (((v2_tops_1 @ sk_B @ sk_A)
% 0.62/0.84        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.62/0.84      inference('demod', [status(thm)], ['29', '30'])).
% 0.62/0.84  thf('32', plain,
% 0.62/0.84      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.62/0.84         <= ((![X21 : $i]:
% 0.62/0.84                (((X21) = (k1_xboole_0))
% 0.62/0.84                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.84                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.62/0.84                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['26', '31'])).
% 0.62/0.84  thf('33', plain,
% 0.62/0.84      (((v2_tops_1 @ sk_B @ sk_A))
% 0.62/0.84         <= ((![X21 : $i]:
% 0.62/0.84                (((X21) = (k1_xboole_0))
% 0.62/0.84                 | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.84                 | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.62/0.84                 | ~ (r1_tarski @ X21 @ sk_B))))),
% 0.62/0.84      inference('simplify', [status(thm)], ['32'])).
% 0.62/0.84  thf('34', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('35', plain,
% 0.62/0.84      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.62/0.84      inference('split', [status(esa)], ['34'])).
% 0.62/0.84  thf('36', plain,
% 0.62/0.84      (~
% 0.62/0.84       (![X21 : $i]:
% 0.62/0.84          (((X21) = (k1_xboole_0))
% 0.62/0.84           | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.84           | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.62/0.84           | ~ (r1_tarski @ X21 @ sk_B))) | 
% 0.62/0.84       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['33', '35'])).
% 0.62/0.84  thf('37', plain,
% 0.62/0.84      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.62/0.84      inference('split', [status(esa)], ['34'])).
% 0.62/0.84  thf('38', plain,
% 0.62/0.84      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('39', plain,
% 0.62/0.84      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.62/0.84      inference('split', [status(esa)], ['38'])).
% 0.62/0.84  thf('40', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('41', plain,
% 0.62/0.84      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.62/0.84      inference('split', [status(esa)], ['40'])).
% 0.62/0.84  thf('42', plain,
% 0.62/0.84      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.84        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('43', plain,
% 0.62/0.84      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.62/0.84       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.62/0.84      inference('split', [status(esa)], ['42'])).
% 0.62/0.84  thf('44', plain,
% 0.62/0.84      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.62/0.84      inference('split', [status(esa)], ['0'])).
% 0.62/0.84  thf('45', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('46', plain,
% 0.62/0.84      (![X19 : $i, X20 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.62/0.84          | ~ (v2_tops_1 @ X19 @ X20)
% 0.62/0.84          | ((k1_tops_1 @ X20 @ X19) = (k1_xboole_0))
% 0.62/0.84          | ~ (l1_pre_topc @ X20))),
% 0.62/0.84      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.62/0.84  thf('47', plain,
% 0.62/0.84      ((~ (l1_pre_topc @ sk_A)
% 0.62/0.84        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.62/0.84        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['45', '46'])).
% 0.62/0.84  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('49', plain,
% 0.62/0.84      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.62/0.84        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.62/0.84      inference('demod', [status(thm)], ['47', '48'])).
% 0.62/0.84  thf('50', plain,
% 0.62/0.84      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.62/0.84         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['44', '49'])).
% 0.62/0.84  thf('51', plain,
% 0.62/0.84      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.62/0.84      inference('split', [status(esa)], ['34'])).
% 0.62/0.84  thf('52', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('53', plain,
% 0.62/0.84      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.62/0.84      inference('split', [status(esa)], ['38'])).
% 0.62/0.84  thf('54', plain,
% 0.62/0.84      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.62/0.84         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.62/0.84      inference('split', [status(esa)], ['42'])).
% 0.62/0.84  thf(t56_tops_1, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( l1_pre_topc @ A ) =>
% 0.62/0.84       ( ![B:$i]:
% 0.62/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.84           ( ![C:$i]:
% 0.62/0.84             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.84               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.62/0.84                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.62/0.84  thf('55', plain,
% 0.62/0.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.62/0.84          | ~ (v3_pre_topc @ X16 @ X17)
% 0.62/0.84          | ~ (r1_tarski @ X16 @ X18)
% 0.62/0.84          | (r1_tarski @ X16 @ (k1_tops_1 @ X17 @ X18))
% 0.62/0.84          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.62/0.84          | ~ (l1_pre_topc @ X17))),
% 0.62/0.84      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.62/0.84  thf('56', plain,
% 0.62/0.84      ((![X0 : $i]:
% 0.62/0.84          (~ (l1_pre_topc @ sk_A)
% 0.62/0.84           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.84           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.62/0.84           | ~ (r1_tarski @ sk_C @ X0)
% 0.62/0.84           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.62/0.84         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['54', '55'])).
% 0.62/0.84  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('58', plain,
% 0.62/0.84      ((![X0 : $i]:
% 0.62/0.84          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.84           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.62/0.84           | ~ (r1_tarski @ sk_C @ X0)
% 0.62/0.84           | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.62/0.84         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.62/0.84      inference('demod', [status(thm)], ['56', '57'])).
% 0.62/0.84  thf('59', plain,
% 0.62/0.84      ((![X0 : $i]:
% 0.62/0.84          (~ (r1_tarski @ sk_C @ X0)
% 0.62/0.84           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.62/0.84           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.62/0.84         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.62/0.84             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['53', '58'])).
% 0.62/0.84  thf('60', plain,
% 0.62/0.84      ((((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))
% 0.62/0.84         | ~ (r1_tarski @ sk_C @ sk_B)))
% 0.62/0.84         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.62/0.84             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['52', '59'])).
% 0.62/0.84  thf('61', plain,
% 0.62/0.84      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.62/0.84         <= (((r1_tarski @ sk_C @ sk_B)) & 
% 0.62/0.84             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.62/0.84             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['51', '60'])).
% 0.62/0.84  thf('62', plain,
% 0.62/0.84      (((r1_tarski @ sk_C @ k1_xboole_0))
% 0.62/0.84         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.62/0.84             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.62/0.84             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.62/0.84             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.62/0.84      inference('sup+', [status(thm)], ['50', '61'])).
% 0.62/0.84  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.62/0.84  thf('63', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.62/0.84      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.62/0.84  thf(d10_xboole_0, axiom,
% 0.62/0.84    (![A:$i,B:$i]:
% 0.62/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.62/0.84  thf('64', plain,
% 0.62/0.84      (![X0 : $i, X2 : $i]:
% 0.62/0.84         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.62/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.62/0.84  thf('65', plain,
% 0.62/0.84      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['63', '64'])).
% 0.62/0.84  thf('66', plain,
% 0.62/0.84      ((((sk_C) = (k1_xboole_0)))
% 0.62/0.84         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.62/0.84             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.62/0.84             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.62/0.84             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['62', '65'])).
% 0.62/0.84  thf('67', plain,
% 0.62/0.84      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.62/0.84      inference('split', [status(esa)], ['40'])).
% 0.62/0.84  thf('68', plain,
% 0.62/0.84      ((((sk_C) != (sk_C)))
% 0.62/0.84         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.62/0.84             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.62/0.84             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.62/0.84             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.62/0.84             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['66', '67'])).
% 0.62/0.84  thf('69', plain,
% 0.62/0.84      (~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.62/0.84       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.62/0.84       ~ ((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.62/0.84       (((sk_C) = (k1_xboole_0)))),
% 0.62/0.84      inference('simplify', [status(thm)], ['68'])).
% 0.62/0.84  thf('70', plain, ($false),
% 0.62/0.84      inference('sat_resolution*', [status(thm)],
% 0.62/0.84                ['1', '36', '37', '39', '41', '43', '69'])).
% 0.62/0.84  
% 0.62/0.84  % SZS output end Refutation
% 0.62/0.84  
% 0.62/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
