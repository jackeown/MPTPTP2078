%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xFxBHyi6gk

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:11 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 469 expanded)
%              Number of leaves         :   26 ( 147 expanded)
%              Depth                    :   17
%              Number of atoms          : 1141 (6336 expanded)
%              Number of equality atoms :   52 ( 145 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t82_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v1_tops_1 @ B @ A )
                  & ( v1_tops_1 @ C @ A )
                  & ( v3_pre_topc @ C @ A ) )
               => ( v1_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v1_tops_1 @ B @ A )
                    & ( v1_tops_1 @ C @ A )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( v1_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ X17 @ ( k2_pre_topc @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v1_tops_1 @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = ( k2_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_tops_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ X17 @ ( k2_pre_topc @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v1_tops_1 @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = ( k2_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ X17 @ ( k2_pre_topc @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v1_tops_1 @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( v1_tops_1 @ C @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v1_tops_1 @ X21 @ X22 )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ( v1_tops_1 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t79_tops_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v1_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('56',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v1_tops_1 @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = ( k2_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['42','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t81_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( v3_pre_topc @ C @ A )
                 => ( ( k2_pre_topc @ A @ C )
                    = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X25 )
      | ( ( k2_pre_topc @ X25 @ X26 )
        = ( k2_pre_topc @ X25 @ ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X26 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v1_tops_1 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t81_tops_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ X1 )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ X1 )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X1 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( v1_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','26'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('73',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['71','74','75'])).

thf('77',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_C )
      = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['13','76'])).

thf('78',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('83',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X6 @ X8 @ X7 )
        = ( k9_subset_1 @ X6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('90',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['77','78','89','90'])).

thf('92',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('95',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('96',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k3_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('99',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_pre_topc @ X20 @ X19 )
       != ( k2_struct_0 @ X20 ) )
      | ( v1_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) )
       != ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) )
       != ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['92','103'])).

thf('105',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('106',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v1_tops_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('109',plain,(
    ~ ( v1_tops_1 @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('111',plain,(
    ~ ( v1_tops_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['106','111'])).

thf('113',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['91','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xFxBHyi6gk
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.83/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.04  % Solved by: fo/fo7.sh
% 0.83/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.04  % done 1275 iterations in 0.587s
% 0.83/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.04  % SZS output start Refutation
% 0.83/1.04  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.83/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.83/1.04  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.83/1.04  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.83/1.04  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.83/1.04  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.83/1.04  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.83/1.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.04  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.83/1.04  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.83/1.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.04  thf(sk_C_type, type, sk_C: $i).
% 0.83/1.04  thf(t82_tops_1, conjecture,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.04       ( ![B:$i]:
% 0.83/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.04           ( ![C:$i]:
% 0.83/1.04             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.04               ( ( ( v1_tops_1 @ B @ A ) & ( v1_tops_1 @ C @ A ) & 
% 0.83/1.04                   ( v3_pre_topc @ C @ A ) ) =>
% 0.83/1.04                 ( v1_tops_1 @
% 0.83/1.04                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.83/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.04    (~( ![A:$i]:
% 0.83/1.04        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.04          ( ![B:$i]:
% 0.83/1.04            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.04              ( ![C:$i]:
% 0.83/1.04                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.04                  ( ( ( v1_tops_1 @ B @ A ) & ( v1_tops_1 @ C @ A ) & 
% 0.83/1.04                      ( v3_pre_topc @ C @ A ) ) =>
% 0.83/1.04                    ( v1_tops_1 @
% 0.83/1.04                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.83/1.04    inference('cnf.neg', [status(esa)], [t82_tops_1])).
% 0.83/1.04  thf('0', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(t48_pre_topc, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( l1_pre_topc @ A ) =>
% 0.83/1.04       ( ![B:$i]:
% 0.83/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.04           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.83/1.04  thf('1', plain,
% 0.83/1.04      (![X17 : $i, X18 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.83/1.04          | (r1_tarski @ X17 @ (k2_pre_topc @ X18 @ X17))
% 0.83/1.04          | ~ (l1_pre_topc @ X18))),
% 0.83/1.04      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.83/1.04  thf('2', plain,
% 0.83/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.83/1.04        | (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['0', '1'])).
% 0.83/1.04  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('4', plain, ((r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))),
% 0.83/1.04      inference('demod', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf(t3_subset, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.83/1.04  thf('5', plain,
% 0.83/1.04      (![X12 : $i, X14 : $i]:
% 0.83/1.04         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.04  thf('6', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['4', '5'])).
% 0.83/1.04  thf('7', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(d3_tops_1, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( l1_pre_topc @ A ) =>
% 0.83/1.04       ( ![B:$i]:
% 0.83/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.04           ( ( v1_tops_1 @ B @ A ) <=>
% 0.83/1.04             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.83/1.04  thf('8', plain,
% 0.83/1.04      (![X19 : $i, X20 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.83/1.04          | ~ (v1_tops_1 @ X19 @ X20)
% 0.83/1.04          | ((k2_pre_topc @ X20 @ X19) = (k2_struct_0 @ X20))
% 0.83/1.04          | ~ (l1_pre_topc @ X20))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.83/1.04  thf('9', plain,
% 0.83/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.83/1.04        | ((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))
% 0.83/1.04        | ~ (v1_tops_1 @ sk_C @ sk_A))),
% 0.83/1.04      inference('sup-', [status(thm)], ['7', '8'])).
% 0.83/1.04  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('11', plain, ((v1_tops_1 @ sk_C @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('12', plain, (((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.83/1.04  thf('13', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.83/1.04      inference('demod', [status(thm)], ['6', '12'])).
% 0.83/1.04  thf('14', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('15', plain,
% 0.83/1.04      (![X17 : $i, X18 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.83/1.04          | (r1_tarski @ X17 @ (k2_pre_topc @ X18 @ X17))
% 0.83/1.04          | ~ (l1_pre_topc @ X18))),
% 0.83/1.04      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.83/1.04  thf('16', plain,
% 0.83/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.83/1.04        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['14', '15'])).
% 0.83/1.04  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('18', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['16', '17'])).
% 0.83/1.04  thf('19', plain,
% 0.83/1.04      (![X12 : $i, X14 : $i]:
% 0.83/1.04         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.04  thf('20', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['18', '19'])).
% 0.83/1.04  thf('21', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('22', plain,
% 0.83/1.04      (![X19 : $i, X20 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.83/1.04          | ~ (v1_tops_1 @ X19 @ X20)
% 0.83/1.04          | ((k2_pre_topc @ X20 @ X19) = (k2_struct_0 @ X20))
% 0.83/1.04          | ~ (l1_pre_topc @ X20))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.83/1.04  thf('23', plain,
% 0.83/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.83/1.04        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.83/1.04        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.83/1.04      inference('sup-', [status(thm)], ['21', '22'])).
% 0.83/1.04  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('25', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('26', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.83/1.04  thf('27', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.83/1.04      inference('demod', [status(thm)], ['20', '26'])).
% 0.83/1.04  thf(d10_xboole_0, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.83/1.04  thf('28', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.83/1.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.04  thf('29', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.83/1.04      inference('simplify', [status(thm)], ['28'])).
% 0.83/1.04  thf('30', plain,
% 0.83/1.04      (![X12 : $i, X14 : $i]:
% 0.83/1.04         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.04  thf('31', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['29', '30'])).
% 0.83/1.04  thf('32', plain,
% 0.83/1.04      (![X17 : $i, X18 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.83/1.04          | (r1_tarski @ X17 @ (k2_pre_topc @ X18 @ X17))
% 0.83/1.04          | ~ (l1_pre_topc @ X18))),
% 0.83/1.04      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.83/1.04  thf('33', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (l1_pre_topc @ X0)
% 0.83/1.04          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.83/1.04             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['31', '32'])).
% 0.83/1.04  thf('34', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['29', '30'])).
% 0.83/1.04  thf(dt_k2_pre_topc, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( ( l1_pre_topc @ A ) & 
% 0.83/1.04         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.83/1.04       ( m1_subset_1 @
% 0.83/1.04         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.83/1.04  thf('35', plain,
% 0.83/1.04      (![X15 : $i, X16 : $i]:
% 0.83/1.04         (~ (l1_pre_topc @ X15)
% 0.83/1.04          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.83/1.04          | (m1_subset_1 @ (k2_pre_topc @ X15 @ X16) @ 
% 0.83/1.04             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.83/1.04  thf('36', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.83/1.04           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.83/1.04          | ~ (l1_pre_topc @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['34', '35'])).
% 0.83/1.04  thf('37', plain,
% 0.83/1.04      (![X12 : $i, X13 : $i]:
% 0.83/1.04         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.04  thf('38', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (l1_pre_topc @ X0)
% 0.83/1.04          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.83/1.04             (u1_struct_0 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['36', '37'])).
% 0.83/1.04  thf('39', plain,
% 0.83/1.04      (![X0 : $i, X2 : $i]:
% 0.83/1.04         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.83/1.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.04  thf('40', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (l1_pre_topc @ X0)
% 0.83/1.04          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.83/1.04               (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.83/1.04          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['38', '39'])).
% 0.83/1.04  thf('41', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (l1_pre_topc @ X0)
% 0.83/1.04          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.83/1.04          | ~ (l1_pre_topc @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['33', '40'])).
% 0.83/1.04  thf('42', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.83/1.04          | ~ (l1_pre_topc @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['41'])).
% 0.83/1.04  thf('43', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['29', '30'])).
% 0.83/1.04  thf('44', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(t79_tops_1, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( l1_pre_topc @ A ) =>
% 0.83/1.04       ( ![B:$i]:
% 0.83/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.04           ( ![C:$i]:
% 0.83/1.04             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.04               ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.83/1.04                 ( v1_tops_1 @ C @ A ) ) ) ) ) ) ))).
% 0.83/1.04  thf('45', plain,
% 0.83/1.04      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.83/1.04          | ~ (v1_tops_1 @ X21 @ X22)
% 0.83/1.04          | ~ (r1_tarski @ X21 @ X23)
% 0.83/1.04          | (v1_tops_1 @ X23 @ X22)
% 0.83/1.04          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.83/1.04          | ~ (l1_pre_topc @ X22))),
% 0.83/1.04      inference('cnf', [status(esa)], [t79_tops_1])).
% 0.83/1.04  thf('46', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (l1_pre_topc @ sk_A)
% 0.83/1.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.04          | (v1_tops_1 @ X0 @ sk_A)
% 0.83/1.04          | ~ (r1_tarski @ sk_B @ X0)
% 0.83/1.04          | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.83/1.04      inference('sup-', [status(thm)], ['44', '45'])).
% 0.83/1.04  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('48', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('49', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.04          | (v1_tops_1 @ X0 @ sk_A)
% 0.83/1.04          | ~ (r1_tarski @ sk_B @ X0))),
% 0.83/1.04      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.83/1.04  thf('50', plain,
% 0.83/1.04      ((~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.83/1.04        | (v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.83/1.04      inference('sup-', [status(thm)], ['43', '49'])).
% 0.83/1.04  thf('51', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('52', plain,
% 0.83/1.04      (![X12 : $i, X13 : $i]:
% 0.83/1.04         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.04  thf('53', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.83/1.04      inference('sup-', [status(thm)], ['51', '52'])).
% 0.83/1.04  thf('54', plain, ((v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.83/1.04      inference('demod', [status(thm)], ['50', '53'])).
% 0.83/1.04  thf('55', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['29', '30'])).
% 0.83/1.04  thf('56', plain,
% 0.83/1.04      (![X19 : $i, X20 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.83/1.04          | ~ (v1_tops_1 @ X19 @ X20)
% 0.83/1.04          | ((k2_pre_topc @ X20 @ X19) = (k2_struct_0 @ X20))
% 0.83/1.04          | ~ (l1_pre_topc @ X20))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.83/1.04  thf('57', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (l1_pre_topc @ X0)
% 0.83/1.04          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.83/1.04          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['55', '56'])).
% 0.83/1.04  thf('58', plain,
% 0.83/1.04      ((((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))
% 0.83/1.04        | ~ (l1_pre_topc @ sk_A))),
% 0.83/1.04      inference('sup-', [status(thm)], ['54', '57'])).
% 0.83/1.04  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('60', plain,
% 0.83/1.04      (((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['58', '59'])).
% 0.83/1.04  thf('61', plain,
% 0.83/1.04      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.83/1.04      inference('sup+', [status(thm)], ['42', '60'])).
% 0.83/1.04  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('63', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['61', '62'])).
% 0.83/1.04  thf(t81_tops_1, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.83/1.04       ( ![B:$i]:
% 0.83/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.04           ( ( v1_tops_1 @ B @ A ) =>
% 0.83/1.04             ( ![C:$i]:
% 0.83/1.04               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.83/1.04                 ( ( v3_pre_topc @ C @ A ) =>
% 0.83/1.04                   ( ( k2_pre_topc @ A @ C ) =
% 0.83/1.04                     ( k2_pre_topc @
% 0.83/1.04                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.83/1.04  thf('64', plain,
% 0.83/1.04      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.83/1.04          | ~ (v3_pre_topc @ X26 @ X25)
% 0.83/1.04          | ((k2_pre_topc @ X25 @ X26)
% 0.83/1.04              = (k2_pre_topc @ X25 @ 
% 0.83/1.04                 (k9_subset_1 @ (u1_struct_0 @ X25) @ X26 @ X24)))
% 0.83/1.04          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.83/1.04          | ~ (v1_tops_1 @ X24 @ X25)
% 0.83/1.04          | ~ (l1_pre_topc @ X25)
% 0.83/1.04          | ~ (v2_pre_topc @ X25))),
% 0.83/1.04      inference('cnf', [status(esa)], [t81_tops_1])).
% 0.83/1.04  thf('65', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.83/1.04          | ~ (v2_pre_topc @ sk_A)
% 0.83/1.04          | ~ (l1_pre_topc @ sk_A)
% 0.83/1.04          | ~ (v1_tops_1 @ X0 @ sk_A)
% 0.83/1.04          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.83/1.04          | ((k2_pre_topc @ sk_A @ X1)
% 0.83/1.04              = (k2_pre_topc @ sk_A @ 
% 0.83/1.04                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ X0)))
% 0.83/1.04          | ~ (v3_pre_topc @ X1 @ sk_A))),
% 0.83/1.04      inference('sup-', [status(thm)], ['63', '64'])).
% 0.83/1.04  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('68', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['61', '62'])).
% 0.83/1.04  thf('69', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['61', '62'])).
% 0.83/1.04  thf('70', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.83/1.04          | ~ (v1_tops_1 @ X0 @ sk_A)
% 0.83/1.04          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.83/1.04          | ((k2_pre_topc @ sk_A @ X1)
% 0.83/1.04              = (k2_pre_topc @ sk_A @ 
% 0.83/1.04                 (k9_subset_1 @ (k2_struct_0 @ sk_A) @ X1 @ X0)))
% 0.83/1.04          | ~ (v3_pre_topc @ X1 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.83/1.04  thf('71', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v3_pre_topc @ X0 @ sk_A)
% 0.83/1.04          | ((k2_pre_topc @ sk_A @ X0)
% 0.83/1.04              = (k2_pre_topc @ sk_A @ 
% 0.83/1.04                 (k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_B)))
% 0.83/1.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.83/1.04          | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.83/1.04      inference('sup-', [status(thm)], ['27', '70'])).
% 0.83/1.04  thf('72', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.83/1.04      inference('demod', [status(thm)], ['20', '26'])).
% 0.83/1.04  thf(redefinition_k9_subset_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.83/1.04       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.83/1.04  thf('73', plain,
% 0.83/1.04      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.83/1.04         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.83/1.04          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.83/1.04      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.83/1.04  thf('74', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.83/1.04           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.83/1.04      inference('sup-', [status(thm)], ['72', '73'])).
% 0.83/1.04  thf('75', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('76', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v3_pre_topc @ X0 @ sk_A)
% 0.83/1.04          | ((k2_pre_topc @ sk_A @ X0)
% 0.83/1.04              = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))
% 0.83/1.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 0.83/1.04      inference('demod', [status(thm)], ['71', '74', '75'])).
% 0.83/1.04  thf('77', plain,
% 0.83/1.04      ((((k2_pre_topc @ sk_A @ sk_C)
% 0.83/1.04          = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))
% 0.83/1.04        | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.83/1.04      inference('sup-', [status(thm)], ['13', '76'])).
% 0.83/1.04  thf('78', plain, (((k2_pre_topc @ sk_A @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.83/1.04  thf('79', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('80', plain,
% 0.83/1.04      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.83/1.04         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.83/1.04          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.83/1.04      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.83/1.04  thf('81', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.83/1.04           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.83/1.04      inference('sup-', [status(thm)], ['79', '80'])).
% 0.83/1.04  thf('82', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(commutativity_k9_subset_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.83/1.04       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.83/1.04  thf('83', plain,
% 0.83/1.04      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.83/1.04         (((k9_subset_1 @ X6 @ X8 @ X7) = (k9_subset_1 @ X6 @ X7 @ X8))
% 0.83/1.04          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.83/1.04      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.83/1.04  thf('84', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.83/1.04           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['82', '83'])).
% 0.83/1.04  thf('85', plain,
% 0.83/1.04      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.83/1.04         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['81', '84'])).
% 0.83/1.04  thf('86', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('87', plain,
% 0.83/1.04      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.83/1.04         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.83/1.04          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.83/1.04      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.83/1.04  thf('88', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.83/1.04           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.83/1.04      inference('sup-', [status(thm)], ['86', '87'])).
% 0.83/1.04  thf('89', plain,
% 0.83/1.04      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['85', '88'])).
% 0.83/1.04  thf('90', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('91', plain,
% 0.83/1.04      (((k2_struct_0 @ sk_A)
% 0.83/1.04         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.83/1.04      inference('demod', [status(thm)], ['77', '78', '89', '90'])).
% 0.83/1.04  thf('92', plain,
% 0.83/1.04      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['85', '88'])).
% 0.83/1.04  thf('93', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('94', plain,
% 0.83/1.04      (![X12 : $i, X13 : $i]:
% 0.83/1.04         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.04  thf('95', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.83/1.04      inference('sup-', [status(thm)], ['93', '94'])).
% 0.83/1.04  thf(t108_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.83/1.04  thf('96', plain,
% 0.83/1.04      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.83/1.04         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k3_xboole_0 @ X3 @ X5) @ X4))),
% 0.83/1.04      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.83/1.04  thf('97', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (r1_tarski @ (k3_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 0.83/1.04      inference('sup-', [status(thm)], ['95', '96'])).
% 0.83/1.04  thf('98', plain,
% 0.83/1.04      (![X12 : $i, X14 : $i]:
% 0.83/1.04         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.04  thf('99', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (m1_subset_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 0.83/1.04          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['97', '98'])).
% 0.83/1.04  thf('100', plain,
% 0.83/1.04      (![X19 : $i, X20 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.83/1.04          | ((k2_pre_topc @ X20 @ X19) != (k2_struct_0 @ X20))
% 0.83/1.04          | (v1_tops_1 @ X19 @ X20)
% 0.83/1.04          | ~ (l1_pre_topc @ X20))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.83/1.04  thf('101', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (l1_pre_topc @ sk_A)
% 0.83/1.04          | (v1_tops_1 @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 0.83/1.04          | ((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0))
% 0.83/1.04              != (k2_struct_0 @ sk_A)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['99', '100'])).
% 0.83/1.04  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('103', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_tops_1 @ (k3_xboole_0 @ sk_C @ X0) @ sk_A)
% 0.83/1.04          | ((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ X0))
% 0.83/1.04              != (k2_struct_0 @ sk_A)))),
% 0.83/1.04      inference('demod', [status(thm)], ['101', '102'])).
% 0.83/1.04  thf('104', plain,
% 0.83/1.04      ((((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.83/1.04          != (k2_struct_0 @ sk_A))
% 0.83/1.04        | (v1_tops_1 @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.83/1.04      inference('sup-', [status(thm)], ['92', '103'])).
% 0.83/1.04  thf('105', plain,
% 0.83/1.04      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['85', '88'])).
% 0.83/1.04  thf('106', plain,
% 0.83/1.04      ((((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.83/1.04          != (k2_struct_0 @ sk_A))
% 0.83/1.04        | (v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['104', '105'])).
% 0.83/1.04  thf('107', plain,
% 0.83/1.04      (~ (v1_tops_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('108', plain,
% 0.83/1.04      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.83/1.04         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['81', '84'])).
% 0.83/1.04  thf('109', plain, (~ (v1_tops_1 @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A)),
% 0.83/1.04      inference('demod', [status(thm)], ['107', '108'])).
% 0.83/1.04  thf('110', plain,
% 0.83/1.04      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['85', '88'])).
% 0.83/1.04  thf('111', plain, (~ (v1_tops_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.83/1.04      inference('demod', [status(thm)], ['109', '110'])).
% 0.83/1.04  thf('112', plain,
% 0.83/1.04      (((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.83/1.04         != (k2_struct_0 @ sk_A))),
% 0.83/1.04      inference('clc', [status(thm)], ['106', '111'])).
% 0.83/1.04  thf('113', plain, ($false),
% 0.83/1.04      inference('simplify_reflect-', [status(thm)], ['91', '112'])).
% 0.83/1.04  
% 0.83/1.04  % SZS output end Refutation
% 0.83/1.04  
% 0.83/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
