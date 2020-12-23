%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kSliDQzCaK

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:20 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 201 expanded)
%              Number of leaves         :   23 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          : 1115 (2982 expanded)
%              Number of equality atoms :   45 ( 116 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
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

thf('4',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X23 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X23 @ sk_A )
      | ~ ( r1_tarski @ X23 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tops_1 @ X21 @ X22 )
      | ( ( k1_tops_1 @ X22 @ X21 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['6'])).

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

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( ( k1_tops_1 @ X17 @ X18 )
        = X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('19',plain,
    ( ! [X17: $i,X18: $i] :
        ( ~ ( l1_pre_topc @ X17 )
        | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( v3_pre_topc @ X18 @ X17 )
        | ( ( k1_tops_1 @ X17 @ X18 )
          = X18 ) )
   <= ! [X17: $i,X18: $i] :
        ( ~ ( l1_pre_topc @ X17 )
        | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( v3_pre_topc @ X18 @ X17 )
        | ( ( k1_tops_1 @ X17 @ X18 )
          = X18 ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( ( k1_tops_1 @ X17 @ X18 )
        = X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('22',plain,
    ( ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) )
   <= ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ~ ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ! [X17: $i,X18: $i] :
        ( ~ ( l1_pre_topc @ X17 )
        | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( v3_pre_topc @ X18 @ X17 )
        | ( ( k1_tops_1 @ X17 @ X18 )
          = X18 ) )
    | ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( ( k1_tops_1 @ X17 @ X18 )
        = X18 ) ) ),
    inference('sat_resolution*',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( ( k1_tops_1 @ X17 @ X18 )
        = X18 ) ) ),
    inference(simpl_trail,[status(thm)],['19','28'])).

thf('30',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C )
        = sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C )
        = sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r1_tarski @ X14 @ X16 )
      | ( r1_tarski @ ( k1_tops_1 @ X15 @ X14 ) @ ( k1_tops_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ~ ( r1_tarski @ sk_C @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['34','47'])).

thf('49',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['33','50'])).

thf('52',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['15','51'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('53',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('58',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('61',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X13 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
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
    inference(split,[status(esa)],['8'])).

thf('73',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['64','65'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('76',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('77',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k1_tops_1 @ X22 @ X21 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ~ ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','59','60','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kSliDQzCaK
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 726 iterations in 0.231s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.68  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.68  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.68  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.46/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.68  thf(t86_tops_1, conjecture,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68           ( ( v2_tops_1 @ B @ A ) <=>
% 0.46/0.68             ( ![C:$i]:
% 0.46/0.68               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.46/0.68                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i]:
% 0.46/0.68        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.68          ( ![B:$i]:
% 0.46/0.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68              ( ( v2_tops_1 @ B @ A ) <=>
% 0.46/0.68                ( ![C:$i]:
% 0.46/0.68                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.46/0.68                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.46/0.68  thf('0', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('1', plain,
% 0.46/0.68      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf('2', plain,
% 0.46/0.68      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('split', [status(esa)], ['2'])).
% 0.46/0.68  thf('4', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('split', [status(esa)], ['4'])).
% 0.46/0.68  thf('6', plain,
% 0.46/0.68      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.68        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.46/0.68       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('split', [status(esa)], ['6'])).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      (![X23 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.68          | ((X23) = (k1_xboole_0))
% 0.46/0.68          | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.46/0.68          | ~ (r1_tarski @ X23 @ sk_B)
% 0.46/0.68          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.46/0.68      inference('split', [status(esa)], ['8'])).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t84_tops_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68           ( ( v2_tops_1 @ B @ A ) <=>
% 0.46/0.68             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.46/0.68          | ~ (v2_tops_1 @ X21 @ X22)
% 0.46/0.68          | ((k1_tops_1 @ X22 @ X21) = (k1_xboole_0))
% 0.46/0.68          | ~ (l1_pre_topc @ X22))),
% 0.46/0.68      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.68        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.68        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.68  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.46/0.68        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.46/0.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['9', '14'])).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.46/0.68      inference('split', [status(esa)], ['2'])).
% 0.46/0.68  thf('17', plain,
% 0.46/0.68      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.68         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.68      inference('split', [status(esa)], ['6'])).
% 0.46/0.68  thf(t55_tops_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( l1_pre_topc @ B ) =>
% 0.46/0.68           ( ![C:$i]:
% 0.46/0.68             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68               ( ![D:$i]:
% 0.46/0.68                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.68                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.46/0.68                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.46/0.68                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.46/0.68                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.68  thf('18', plain,
% 0.46/0.68      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X17)
% 0.46/0.68          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.68          | ~ (v3_pre_topc @ X18 @ X17)
% 0.46/0.68          | ((k1_tops_1 @ X17 @ X18) = (X18))
% 0.46/0.68          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.68          | ~ (l1_pre_topc @ X20)
% 0.46/0.68          | ~ (v2_pre_topc @ X20))),
% 0.46/0.68      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      ((![X17 : $i, X18 : $i]:
% 0.46/0.68          (~ (l1_pre_topc @ X17)
% 0.46/0.68           | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.68           | ~ (v3_pre_topc @ X18 @ X17)
% 0.46/0.68           | ((k1_tops_1 @ X17 @ X18) = (X18))))
% 0.46/0.68         <= ((![X17 : $i, X18 : $i]:
% 0.46/0.68                (~ (l1_pre_topc @ X17)
% 0.46/0.68                 | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.68                 | ~ (v3_pre_topc @ X18 @ X17)
% 0.46/0.68                 | ((k1_tops_1 @ X17 @ X18) = (X18)))))),
% 0.46/0.68      inference('split', [status(esa)], ['18'])).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X17)
% 0.46/0.68          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.68          | ~ (v3_pre_topc @ X18 @ X17)
% 0.46/0.68          | ((k1_tops_1 @ X17 @ X18) = (X18))
% 0.46/0.68          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.68          | ~ (l1_pre_topc @ X20)
% 0.46/0.68          | ~ (v2_pre_topc @ X20))),
% 0.46/0.68      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.46/0.68  thf('22', plain,
% 0.46/0.68      ((![X19 : $i, X20 : $i]:
% 0.46/0.68          (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.68           | ~ (l1_pre_topc @ X20)
% 0.46/0.68           | ~ (v2_pre_topc @ X20)))
% 0.46/0.68         <= ((![X19 : $i, X20 : $i]:
% 0.46/0.68                (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.68                 | ~ (l1_pre_topc @ X20)
% 0.46/0.68                 | ~ (v2_pre_topc @ X20))))),
% 0.46/0.68      inference('split', [status(esa)], ['21'])).
% 0.46/0.68  thf('23', plain,
% 0.46/0.68      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.46/0.68         <= ((![X19 : $i, X20 : $i]:
% 0.46/0.68                (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.68                 | ~ (l1_pre_topc @ X20)
% 0.46/0.68                 | ~ (v2_pre_topc @ X20))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['20', '22'])).
% 0.46/0.68  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('26', plain,
% 0.46/0.68      (~
% 0.46/0.68       (![X19 : $i, X20 : $i]:
% 0.46/0.68          (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.68           | ~ (l1_pre_topc @ X20)
% 0.46/0.68           | ~ (v2_pre_topc @ X20)))),
% 0.46/0.68      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      ((![X17 : $i, X18 : $i]:
% 0.46/0.68          (~ (l1_pre_topc @ X17)
% 0.46/0.68           | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.68           | ~ (v3_pre_topc @ X18 @ X17)
% 0.46/0.68           | ((k1_tops_1 @ X17 @ X18) = (X18)))) | 
% 0.46/0.68       (![X19 : $i, X20 : $i]:
% 0.46/0.68          (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.68           | ~ (l1_pre_topc @ X20)
% 0.46/0.68           | ~ (v2_pre_topc @ X20)))),
% 0.46/0.68      inference('split', [status(esa)], ['21'])).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      ((![X17 : $i, X18 : $i]:
% 0.46/0.68          (~ (l1_pre_topc @ X17)
% 0.46/0.68           | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.68           | ~ (v3_pre_topc @ X18 @ X17)
% 0.46/0.68           | ((k1_tops_1 @ X17 @ X18) = (X18))))),
% 0.46/0.68      inference('sat_resolution*', [status(thm)], ['26', '27'])).
% 0.46/0.68  thf('29', plain,
% 0.46/0.68      (![X17 : $i, X18 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X17)
% 0.46/0.68          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.68          | ~ (v3_pre_topc @ X18 @ X17)
% 0.46/0.68          | ((k1_tops_1 @ X17 @ X18) = (X18)))),
% 0.46/0.68      inference('simpl_trail', [status(thm)], ['19', '28'])).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))
% 0.46/0.68         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.46/0.68         | ~ (l1_pre_topc @ sk_A)))
% 0.46/0.68         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['17', '29'])).
% 0.46/0.68  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('32', plain,
% 0.46/0.68      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.46/0.68         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.68      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.68  thf('33', plain,
% 0.46/0.68      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.46/0.68         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.46/0.68             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['16', '32'])).
% 0.46/0.68  thf('34', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('35', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t3_subset, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.68  thf('36', plain,
% 0.46/0.68      (![X7 : $i, X8 : $i]:
% 0.46/0.68         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.68  thf('37', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.68  thf('38', plain,
% 0.46/0.68      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf(t1_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.68       ( r1_tarski @ A @ C ) ))).
% 0.46/0.68  thf('39', plain,
% 0.46/0.68      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X3 @ X4)
% 0.46/0.68          | ~ (r1_tarski @ X4 @ X5)
% 0.46/0.68          | (r1_tarski @ X3 @ X5))),
% 0.46/0.68      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.68  thf('40', plain,
% 0.46/0.68      ((![X0 : $i]: ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ sk_B @ X0)))
% 0.46/0.68         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.68  thf('41', plain,
% 0.46/0.68      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.46/0.68         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['37', '40'])).
% 0.46/0.68  thf('42', plain,
% 0.46/0.68      (![X7 : $i, X9 : $i]:
% 0.46/0.68         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.68  thf('43', plain,
% 0.46/0.68      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.68         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.68  thf(t48_tops_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68           ( ![C:$i]:
% 0.46/0.68             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68               ( ( r1_tarski @ B @ C ) =>
% 0.46/0.68                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.46/0.68  thf('44', plain,
% 0.46/0.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.68          | ~ (r1_tarski @ X14 @ X16)
% 0.46/0.68          | (r1_tarski @ (k1_tops_1 @ X15 @ X14) @ (k1_tops_1 @ X15 @ X16))
% 0.46/0.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.68          | ~ (l1_pre_topc @ X15))),
% 0.46/0.68      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.46/0.68  thf('45', plain,
% 0.46/0.68      ((![X0 : $i]:
% 0.46/0.68          (~ (l1_pre_topc @ sk_A)
% 0.46/0.68           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.68           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.46/0.68           | ~ (r1_tarski @ sk_C @ X0)))
% 0.46/0.68         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.68  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('47', plain,
% 0.46/0.68      ((![X0 : $i]:
% 0.46/0.68          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.68           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.46/0.68           | ~ (r1_tarski @ sk_C @ X0)))
% 0.46/0.68         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.46/0.68      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.68  thf('48', plain,
% 0.46/0.68      (((~ (r1_tarski @ sk_C @ sk_B)
% 0.46/0.68         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.68         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['34', '47'])).
% 0.46/0.68  thf('49', plain,
% 0.46/0.68      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf('50', plain,
% 0.46/0.68      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.46/0.68         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.46/0.68      inference('demod', [status(thm)], ['48', '49'])).
% 0.46/0.68  thf('51', plain,
% 0.46/0.68      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.46/0.68         <= (((r1_tarski @ sk_C @ sk_B)) & 
% 0.46/0.68             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.46/0.68             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['33', '50'])).
% 0.46/0.68  thf('52', plain,
% 0.46/0.68      (((r1_tarski @ sk_C @ k1_xboole_0))
% 0.46/0.68         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.46/0.68             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.46/0.68             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.46/0.68             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['15', '51'])).
% 0.46/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.68  thf('53', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.46/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.68  thf(d10_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.68  thf('54', plain,
% 0.46/0.68      (![X0 : $i, X2 : $i]:
% 0.46/0.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.68  thf('55', plain,
% 0.46/0.68      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.68  thf('56', plain,
% 0.46/0.68      ((((sk_C) = (k1_xboole_0)))
% 0.46/0.68         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.46/0.68             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.46/0.68             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.46/0.68             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['52', '55'])).
% 0.46/0.68  thf('57', plain,
% 0.46/0.68      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.46/0.68      inference('split', [status(esa)], ['4'])).
% 0.46/0.68  thf('58', plain,
% 0.46/0.68      ((((sk_C) != (sk_C)))
% 0.46/0.68         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.46/0.68             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.46/0.68             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.46/0.68             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.46/0.68             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.68  thf('59', plain,
% 0.46/0.68      (~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.46/0.68       ~ ((v2_tops_1 @ sk_B @ sk_A)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.46/0.68       ~ ((r1_tarski @ sk_C @ sk_B)) | (((sk_C) = (k1_xboole_0)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['58'])).
% 0.46/0.68  thf('60', plain,
% 0.46/0.68      ((![X23 : $i]:
% 0.46/0.68          (((X23) = (k1_xboole_0))
% 0.46/0.68           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.68           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.46/0.68           | ~ (r1_tarski @ X23 @ sk_B))) | 
% 0.46/0.68       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('split', [status(esa)], ['8'])).
% 0.46/0.68  thf('61', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.68  thf('62', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t44_tops_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.46/0.68  thf('63', plain,
% 0.46/0.68      (![X12 : $i, X13 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.46/0.68          | (r1_tarski @ (k1_tops_1 @ X13 @ X12) @ X12)
% 0.46/0.68          | ~ (l1_pre_topc @ X13))),
% 0.46/0.68      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.46/0.68  thf('64', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.46/0.68      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.68  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('66', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.46/0.68      inference('demod', [status(thm)], ['64', '65'])).
% 0.46/0.68  thf('67', plain,
% 0.46/0.68      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X3 @ X4)
% 0.46/0.68          | ~ (r1_tarski @ X4 @ X5)
% 0.46/0.68          | (r1_tarski @ X3 @ X5))),
% 0.46/0.68      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.68  thf('68', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.46/0.68          | ~ (r1_tarski @ sk_B @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['66', '67'])).
% 0.46/0.68  thf('69', plain,
% 0.46/0.68      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['61', '68'])).
% 0.46/0.68  thf('70', plain,
% 0.46/0.68      (![X7 : $i, X9 : $i]:
% 0.46/0.68         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.68  thf('71', plain,
% 0.46/0.68      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['69', '70'])).
% 0.46/0.68  thf('72', plain,
% 0.46/0.68      ((![X23 : $i]:
% 0.46/0.68          (((X23) = (k1_xboole_0))
% 0.46/0.68           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.68           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.46/0.68           | ~ (r1_tarski @ X23 @ sk_B)))
% 0.46/0.68         <= ((![X23 : $i]:
% 0.46/0.68                (((X23) = (k1_xboole_0))
% 0.46/0.68                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.68                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.46/0.68                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.46/0.68      inference('split', [status(esa)], ['8'])).
% 0.46/0.68  thf('73', plain,
% 0.46/0.68      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.46/0.68         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.46/0.68         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.46/0.68         <= ((![X23 : $i]:
% 0.46/0.68                (((X23) = (k1_xboole_0))
% 0.46/0.68                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.68                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.46/0.68                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['71', '72'])).
% 0.46/0.68  thf('74', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.46/0.68      inference('demod', [status(thm)], ['64', '65'])).
% 0.46/0.68  thf('75', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(fc9_tops_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.46/0.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.68       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.46/0.68  thf('76', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X10)
% 0.46/0.68          | ~ (v2_pre_topc @ X10)
% 0.46/0.68          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.46/0.68          | (v3_pre_topc @ (k1_tops_1 @ X10 @ X11) @ X10))),
% 0.46/0.68      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.46/0.68  thf('77', plain,
% 0.46/0.68      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.46/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.68  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('80', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.46/0.68      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.46/0.68  thf('81', plain,
% 0.46/0.68      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.46/0.68         <= ((![X23 : $i]:
% 0.46/0.68                (((X23) = (k1_xboole_0))
% 0.46/0.68                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.68                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.46/0.68                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.46/0.68      inference('demod', [status(thm)], ['73', '74', '80'])).
% 0.46/0.68  thf('82', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('83', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.46/0.68          | ((k1_tops_1 @ X22 @ X21) != (k1_xboole_0))
% 0.46/0.68          | (v2_tops_1 @ X21 @ X22)
% 0.46/0.68          | ~ (l1_pre_topc @ X22))),
% 0.46/0.68      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.46/0.68  thf('84', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.68        | (v2_tops_1 @ sk_B @ sk_A)
% 0.46/0.68        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['82', '83'])).
% 0.46/0.68  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('86', plain,
% 0.46/0.68      (((v2_tops_1 @ sk_B @ sk_A)
% 0.46/0.68        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['84', '85'])).
% 0.46/0.68  thf('87', plain,
% 0.46/0.68      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.46/0.68         <= ((![X23 : $i]:
% 0.46/0.68                (((X23) = (k1_xboole_0))
% 0.46/0.68                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.68                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.46/0.68                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['81', '86'])).
% 0.46/0.68  thf('88', plain,
% 0.46/0.68      (((v2_tops_1 @ sk_B @ sk_A))
% 0.46/0.68         <= ((![X23 : $i]:
% 0.46/0.68                (((X23) = (k1_xboole_0))
% 0.46/0.68                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.68                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.46/0.68                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.46/0.68      inference('simplify', [status(thm)], ['87'])).
% 0.46/0.68  thf('89', plain,
% 0.46/0.68      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf('90', plain,
% 0.46/0.68      (~
% 0.46/0.68       (![X23 : $i]:
% 0.46/0.68          (((X23) = (k1_xboole_0))
% 0.46/0.68           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.68           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.46/0.68           | ~ (r1_tarski @ X23 @ sk_B))) | 
% 0.46/0.68       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['88', '89'])).
% 0.46/0.68  thf('91', plain, ($false),
% 0.46/0.68      inference('sat_resolution*', [status(thm)],
% 0.46/0.68                ['1', '3', '5', '7', '59', '60', '90'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
