%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UowIYFiKdR

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:04 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 132 expanded)
%              Number of leaves         :   36 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  628 (1345 expanded)
%              Number of equality atoms :   25 (  51 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t28_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( r2_hidden @ D @ C )
                      <=> ( ( v3_pre_topc @ D @ A )
                          & ( v4_pre_topc @ D @ A )
                          & ( r2_hidden @ B @ D ) ) ) )
                  & ( C = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( r2_hidden @ D @ C )
                        <=> ( ( v3_pre_topc @ D @ A )
                            & ( v4_pre_topc @ D @ A )
                            & ( r2_hidden @ B @ D ) ) ) )
                    & ( C = k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t50_subset_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( r2_hidden @ X8 @ X6 )
      | ( r2_hidden @ X8 @ ( k3_subset_1 @ X7 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_subset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = ( k3_subset_1 @ X4 @ ( k1_subset_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('8',plain,(
    ! [X4: $i] :
      ( X4
      = ( k3_subset_1 @ X4 @ ( k1_subset_1 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v4_pre_topc @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v4_pre_topc @ X20 @ X21 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('24',plain,(
    ! [X19: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X19 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('25',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('27',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('28',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X22: $i] :
      ( ~ ( v3_pre_topc @ X22 @ sk_A )
      | ~ ( v4_pre_topc @ X22 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X22 )
      | ( r2_hidden @ X22 @ sk_C )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X22: $i] :
      ( ~ ( v3_pre_topc @ X22 @ sk_A )
      | ~ ( v4_pre_topc @ X22 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X22 )
      | ( r2_hidden @ X22 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('35',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','45'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('48',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('52',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('55',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('56',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['34','35'])).

thf('59',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UowIYFiKdR
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:15:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 183 iterations in 0.062s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.35/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.35/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.35/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.35/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.55  thf(t28_connsp_2, conjecture,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @
% 0.35/0.55                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.55               ( ~( ( ![D:$i]:
% 0.35/0.55                      ( ( m1_subset_1 @
% 0.35/0.55                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55                        ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.55                          ( ( v3_pre_topc @ D @ A ) & 
% 0.35/0.55                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.35/0.55                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i]:
% 0.35/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.55            ( l1_pre_topc @ A ) ) =>
% 0.35/0.55          ( ![B:$i]:
% 0.35/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55              ( ![C:$i]:
% 0.35/0.55                ( ( m1_subset_1 @
% 0.35/0.55                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.55                  ( ~( ( ![D:$i]:
% 0.35/0.55                         ( ( m1_subset_1 @
% 0.35/0.55                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55                           ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.55                             ( ( v3_pre_topc @ D @ A ) & 
% 0.35/0.55                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.35/0.55                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.35/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t4_subset_1, axiom,
% 0.35/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.35/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.35/0.55  thf(t50_subset_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @ C @ A ) =>
% 0.35/0.55               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.35/0.55                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.35/0.55          | (r2_hidden @ X8 @ X6)
% 0.35/0.55          | (r2_hidden @ X8 @ (k3_subset_1 @ X7 @ X6))
% 0.35/0.55          | ~ (m1_subset_1 @ X8 @ X7)
% 0.35/0.55          | ((X7) = (k1_xboole_0)))),
% 0.35/0.55      inference('cnf', [status(esa)], [t50_subset_1])).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((X0) = (k1_xboole_0))
% 0.35/0.55          | ~ (m1_subset_1 @ X1 @ X0)
% 0.35/0.55          | (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.35/0.55          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.55  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.55  thf('5', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.35/0.55  thf(t22_subset_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.35/0.55  thf('6', plain,
% 0.35/0.55      (![X4 : $i]:
% 0.35/0.55         ((k2_subset_1 @ X4) = (k3_subset_1 @ X4 @ (k1_subset_1 @ X4)))),
% 0.35/0.55      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.35/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.35/0.55  thf('7', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.35/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      (![X4 : $i]: ((X4) = (k3_subset_1 @ X4 @ (k1_subset_1 @ X4)))),
% 0.35/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.35/0.55  thf('9', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.35/0.55      inference('sup+', [status(thm)], ['5', '8'])).
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (((X0) = (k1_xboole_0))
% 0.35/0.55          | ~ (m1_subset_1 @ X1 @ X0)
% 0.35/0.55          | (r2_hidden @ X1 @ X0)
% 0.35/0.55          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.35/0.55      inference('demod', [status(thm)], ['4', '9'])).
% 0.35/0.55  thf('11', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ k1_xboole_0)
% 0.35/0.55        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['1', '10'])).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.35/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.35/0.55  thf(cc2_pre_topc, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.35/0.55  thf('13', plain,
% 0.35/0.55      (![X14 : $i, X15 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.35/0.55          | (v4_pre_topc @ X14 @ X15)
% 0.35/0.55          | ~ (v1_xboole_0 @ X14)
% 0.35/0.55          | ~ (l1_pre_topc @ X15)
% 0.35/0.55          | ~ (v2_pre_topc @ X15))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.35/0.55  thf('14', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (~ (v2_pre_topc @ X0)
% 0.35/0.55          | ~ (l1_pre_topc @ X0)
% 0.35/0.55          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.35/0.55          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.35/0.55  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (~ (v2_pre_topc @ X0)
% 0.35/0.55          | ~ (l1_pre_topc @ X0)
% 0.35/0.55          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.35/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.35/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.35/0.55  thf(t29_tops_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( l1_pre_topc @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55           ( ( v4_pre_topc @ B @ A ) <=>
% 0.35/0.55             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.35/0.55  thf('18', plain,
% 0.35/0.55      (![X20 : $i, X21 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.35/0.55          | ~ (v4_pre_topc @ X20 @ X21)
% 0.35/0.55          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.35/0.55          | ~ (l1_pre_topc @ X21))),
% 0.35/0.55      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.35/0.55  thf('19', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (~ (l1_pre_topc @ X0)
% 0.35/0.55          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ 
% 0.35/0.55             X0)
% 0.35/0.55          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.55  thf('20', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.35/0.55      inference('sup+', [status(thm)], ['5', '8'])).
% 0.35/0.55  thf('21', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (~ (l1_pre_topc @ X0)
% 0.35/0.55          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.35/0.55          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.35/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.55  thf('22', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (~ (l1_pre_topc @ X0)
% 0.35/0.55          | ~ (v2_pre_topc @ X0)
% 0.35/0.55          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.35/0.55          | ~ (l1_pre_topc @ X0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['16', '21'])).
% 0.35/0.55  thf('23', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.35/0.55          | ~ (v2_pre_topc @ X0)
% 0.35/0.55          | ~ (l1_pre_topc @ X0))),
% 0.35/0.55      inference('simplify', [status(thm)], ['22'])).
% 0.35/0.55  thf(fc4_pre_topc, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.35/0.55  thf('24', plain,
% 0.35/0.55      (![X19 : $i]:
% 0.35/0.55         ((v4_pre_topc @ (k2_struct_0 @ X19) @ X19)
% 0.35/0.55          | ~ (l1_pre_topc @ X19)
% 0.35/0.55          | ~ (v2_pre_topc @ X19))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.35/0.55  thf(d3_struct_0, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.35/0.55  thf('25', plain,
% 0.35/0.55      (![X16 : $i]:
% 0.35/0.55         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.55  thf(dt_k2_subset_1, axiom,
% 0.35/0.55    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.35/0.55  thf('27', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.35/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.55  thf('28', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.35/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.35/0.55  thf('29', plain,
% 0.35/0.55      (![X22 : $i]:
% 0.35/0.55         (~ (v3_pre_topc @ X22 @ sk_A)
% 0.35/0.55          | ~ (v4_pre_topc @ X22 @ sk_A)
% 0.35/0.55          | ~ (r2_hidden @ sk_B @ X22)
% 0.35/0.55          | (r2_hidden @ X22 @ sk_C)
% 0.35/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('30', plain, (((sk_C) = (k1_xboole_0))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('31', plain,
% 0.35/0.55      (![X22 : $i]:
% 0.35/0.55         (~ (v3_pre_topc @ X22 @ sk_A)
% 0.35/0.55          | ~ (v4_pre_topc @ X22 @ sk_A)
% 0.35/0.55          | ~ (r2_hidden @ sk_B @ X22)
% 0.35/0.55          | (r2_hidden @ X22 @ k1_xboole_0)
% 0.35/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.35/0.55  thf('32', plain,
% 0.35/0.55      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.35/0.55        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.35/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['28', '31'])).
% 0.35/0.55  thf('33', plain,
% 0.35/0.55      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.35/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.35/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.35/0.55        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['25', '32'])).
% 0.35/0.55  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(dt_l1_pre_topc, axiom,
% 0.35/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.35/0.55  thf('35', plain,
% 0.35/0.55      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.55  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.35/0.55  thf('37', plain,
% 0.35/0.55      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.35/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.35/0.55        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.35/0.55      inference('demod', [status(thm)], ['33', '36'])).
% 0.35/0.55  thf('38', plain,
% 0.35/0.55      ((~ (v2_pre_topc @ sk_A)
% 0.35/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.35/0.55        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['24', '37'])).
% 0.35/0.55  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('41', plain,
% 0.35/0.55      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.35/0.55        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.35/0.55  thf('42', plain,
% 0.35/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['23', '41'])).
% 0.35/0.55  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('45', plain,
% 0.35/0.55      ((~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.35/0.55      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.35/0.55  thf('46', plain,
% 0.35/0.55      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.35/0.55        | (r2_hidden @ sk_B @ k1_xboole_0)
% 0.35/0.55        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['11', '45'])).
% 0.35/0.55  thf(t7_ordinal1, axiom,
% 0.35/0.55    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.55  thf('47', plain,
% 0.35/0.55      (![X12 : $i, X13 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.35/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.55  thf('48', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ k1_xboole_0)
% 0.35/0.55        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.35/0.55        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.35/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.55  thf('49', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.35/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.55  thf('50', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ k1_xboole_0)
% 0.35/0.55        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.35/0.55      inference('demod', [status(thm)], ['48', '49'])).
% 0.35/0.55  thf('51', plain,
% 0.35/0.55      (![X12 : $i, X13 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.35/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.55  thf('52', plain,
% 0.35/0.55      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.35/0.55        | ~ (r1_tarski @ k1_xboole_0 @ sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.35/0.55  thf('53', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.35/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.55  thf('54', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.35/0.55      inference('demod', [status(thm)], ['52', '53'])).
% 0.35/0.55  thf(fc2_struct_0, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.35/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.55  thf('55', plain,
% 0.35/0.55      (![X18 : $i]:
% 0.35/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X18))
% 0.35/0.55          | ~ (l1_struct_0 @ X18)
% 0.35/0.55          | (v2_struct_0 @ X18))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.35/0.55  thf('56', plain,
% 0.35/0.55      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.35/0.55        | (v2_struct_0 @ sk_A)
% 0.35/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.35/0.55  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.35/0.55  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.35/0.55  thf('59', plain, ((v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.35/0.55  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.35/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
