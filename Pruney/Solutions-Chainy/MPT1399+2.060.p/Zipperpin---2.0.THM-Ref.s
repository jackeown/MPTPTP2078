%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w7ZBzAEsON

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:10 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 147 expanded)
%              Number of leaves         :   36 (  58 expanded)
%              Depth                    :   24
%              Number of atoms          :  599 (1939 expanded)
%              Number of equality atoms :   30 (  67 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('4',plain,(
    ! [X16: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('7',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X18: $i] :
      ( ~ ( v3_pre_topc @ X18 @ sk_A )
      | ~ ( v4_pre_topc @ X18 @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X18 )
      | ( r2_hidden @ X18 @ sk_C )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('15',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['5','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('24',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['3','28'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_C @ X1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','34'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('37',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_C )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['35','38'])).

thf(rc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( v3_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('41',plain,
    ( ( m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C ) )
    | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('49',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('50',plain,(
    r2_hidden @ ( sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(clc,[status(thm)],['48','49'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('51',plain,(
    ! [X2: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X2 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(t91_orders_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( ( k3_tarski @ A )
           != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( B != k1_xboole_0 )
                & ( r2_hidden @ B @ A ) ) )
      & ~ ( ? [B: $i] :
              ( ( r2_hidden @ B @ A )
              & ( B != k1_xboole_0 ) )
          & ( ( k3_tarski @ A )
            = k1_xboole_0 ) ) ) )).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ( ( k3_tarski @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('53',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = sk_C )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ( ( k3_tarski @ X14 )
       != sk_C ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_C )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( X1 = sk_C ) ) ),
    inference('sup-',[status(thm)],['51','55'])).

thf('57',plain,(
    ! [X1: $i] :
      ( ( X1 = sk_C )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_B_1 @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('60',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['60','63','64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w7ZBzAEsON
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:17:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 242 iterations in 0.150s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.43/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.43/0.61  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.43/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.43/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.43/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.43/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.43/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.43/0.61  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.43/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.43/0.61  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(t28_connsp_2, conjecture,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( m1_subset_1 @
% 0.43/0.61                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.61               ( ~( ( ![D:$i]:
% 0.43/0.61                      ( ( m1_subset_1 @
% 0.43/0.61                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61                        ( ( r2_hidden @ D @ C ) <=>
% 0.43/0.61                          ( ( v3_pre_topc @ D @ A ) & 
% 0.43/0.61                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.43/0.61                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i]:
% 0.43/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.43/0.61            ( l1_pre_topc @ A ) ) =>
% 0.43/0.61          ( ![B:$i]:
% 0.43/0.61            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.61              ( ![C:$i]:
% 0.43/0.61                ( ( m1_subset_1 @
% 0.43/0.61                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.61                  ( ~( ( ![D:$i]:
% 0.43/0.61                         ( ( m1_subset_1 @
% 0.43/0.61                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61                           ( ( r2_hidden @ D @ C ) <=>
% 0.43/0.61                             ( ( v3_pre_topc @ D @ A ) & 
% 0.43/0.61                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.43/0.61                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.43/0.61  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('1', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t2_subset, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ A @ B ) =>
% 0.43/0.61       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]:
% 0.43/0.61         ((r2_hidden @ X6 @ X7)
% 0.43/0.61          | (v1_xboole_0 @ X7)
% 0.43/0.61          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.43/0.61      inference('cnf', [status(esa)], [t2_subset])).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.43/0.61  thf(fc10_tops_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      (![X16 : $i]:
% 0.43/0.61         ((v3_pre_topc @ (k2_struct_0 @ X16) @ X16)
% 0.43/0.61          | ~ (l1_pre_topc @ X16)
% 0.43/0.61          | ~ (v2_pre_topc @ X16))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.43/0.61  thf(d3_struct_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (![X10 : $i]:
% 0.43/0.61         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.61  thf(fc4_pre_topc, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (![X12 : $i]:
% 0.43/0.61         ((v4_pre_topc @ (k2_struct_0 @ X12) @ X12)
% 0.43/0.61          | ~ (l1_pre_topc @ X12)
% 0.43/0.61          | ~ (v2_pre_topc @ X12))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (![X10 : $i]:
% 0.43/0.61         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.43/0.61  thf(dt_k2_subset_1, axiom,
% 0.43/0.61    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.43/0.61  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.43/0.61  thf('9', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.43/0.61      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.43/0.61  thf('10', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.43/0.61      inference('demod', [status(thm)], ['8', '9'])).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      (![X18 : $i]:
% 0.43/0.61         (~ (v3_pre_topc @ X18 @ sk_A)
% 0.43/0.61          | ~ (v4_pre_topc @ X18 @ sk_A)
% 0.43/0.61          | ~ (r2_hidden @ sk_B_2 @ X18)
% 0.43/0.61          | (r2_hidden @ X18 @ sk_C)
% 0.43/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.43/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.43/0.61        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.43/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.43/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.43/0.61      inference('sup-', [status(thm)], ['7', '12'])).
% 0.43/0.61  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(dt_l1_pre_topc, axiom,
% 0.43/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.43/0.61  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.43/0.61        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.43/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.43/0.61      inference('demod', [status(thm)], ['13', '16'])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      ((~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.43/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['6', '17'])).
% 0.43/0.61  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.43/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.43/0.61        | ~ (l1_struct_0 @ sk_A)
% 0.43/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.43/0.61      inference('sup-', [status(thm)], ['5', '21'])).
% 0.43/0.61  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.43/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.43/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      ((~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.43/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['4', '24'])).
% 0.43/0.61  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.43/0.61        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.43/0.61      inference('sup-', [status(thm)], ['3', '28'])).
% 0.43/0.61  thf(t7_ordinal1, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.61  thf('30', plain,
% 0.43/0.61      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.43/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.61        | ~ (r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.43/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.43/0.61  thf('32', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.43/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.43/0.61  thf('33', plain, (((sk_C) = (k1_xboole_0))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('34', plain, (![X1 : $i]: (r1_tarski @ sk_C @ X1)),
% 0.43/0.61      inference('demod', [status(thm)], ['32', '33'])).
% 0.43/0.61  thf('35', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['31', '34'])).
% 0.43/0.61  thf(l13_xboole_0, axiom,
% 0.43/0.61    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.61  thf('36', plain,
% 0.43/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.43/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.43/0.61  thf('37', plain, (((sk_C) = (k1_xboole_0))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('38', plain, (![X0 : $i]: (((X0) = (sk_C)) | ~ (v1_xboole_0 @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['36', '37'])).
% 0.43/0.61  thf('39', plain, (((u1_struct_0 @ sk_A) = (sk_C))),
% 0.43/0.61      inference('sup-', [status(thm)], ['35', '38'])).
% 0.43/0.61  thf(rc3_tops_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ?[B:$i]:
% 0.43/0.61         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.43/0.61           ( ~( v1_xboole_0 @ B ) ) & 
% 0.43/0.61           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      (![X17 : $i]:
% 0.43/0.61         ((m1_subset_1 @ (sk_B_1 @ X17) @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.43/0.61          | ~ (l1_pre_topc @ X17)
% 0.43/0.61          | ~ (v2_pre_topc @ X17)
% 0.43/0.61          | (v2_struct_0 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      (((m1_subset_1 @ (sk_B_1 @ sk_A) @ (k1_zfmisc_1 @ sk_C))
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.61      inference('sup+', [status(thm)], ['39', '40'])).
% 0.43/0.61  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('44', plain,
% 0.43/0.61      (((m1_subset_1 @ (sk_B_1 @ sk_A) @ (k1_zfmisc_1 @ sk_C))
% 0.43/0.61        | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.43/0.61  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('46', plain, ((m1_subset_1 @ (sk_B_1 @ sk_A) @ (k1_zfmisc_1 @ sk_C))),
% 0.43/0.61      inference('clc', [status(thm)], ['44', '45'])).
% 0.43/0.61  thf('47', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]:
% 0.43/0.61         ((r2_hidden @ X6 @ X7)
% 0.43/0.61          | (v1_xboole_0 @ X7)
% 0.43/0.61          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.43/0.61      inference('cnf', [status(esa)], [t2_subset])).
% 0.43/0.61  thf('48', plain,
% 0.43/0.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C))
% 0.43/0.61        | (r2_hidden @ (sk_B_1 @ sk_A) @ (k1_zfmisc_1 @ sk_C)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.43/0.61  thf(fc1_subset_1, axiom,
% 0.43/0.61    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.43/0.61  thf('49', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.43/0.61  thf('50', plain, ((r2_hidden @ (sk_B_1 @ sk_A) @ (k1_zfmisc_1 @ sk_C))),
% 0.43/0.61      inference('clc', [status(thm)], ['48', '49'])).
% 0.43/0.61  thf(t99_zfmisc_1, axiom,
% 0.43/0.61    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.43/0.61  thf('51', plain, (![X2 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X2)) = (X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.43/0.61  thf(t91_orders_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 0.43/0.61            ( ![B:$i]:
% 0.43/0.61              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 0.43/0.61       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.43/0.61            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.43/0.61  thf('52', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         (((X13) = (k1_xboole_0))
% 0.43/0.61          | ~ (r2_hidden @ X13 @ X14)
% 0.43/0.61          | ((k3_tarski @ X14) != (k1_xboole_0)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.43/0.61  thf('53', plain, (((sk_C) = (k1_xboole_0))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('54', plain, (((sk_C) = (k1_xboole_0))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('55', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         (((X13) = (sk_C))
% 0.43/0.61          | ~ (r2_hidden @ X13 @ X14)
% 0.43/0.61          | ((k3_tarski @ X14) != (sk_C)))),
% 0.43/0.61      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.43/0.61  thf('56', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((X0) != (sk_C))
% 0.43/0.61          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 0.43/0.61          | ((X1) = (sk_C)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['51', '55'])).
% 0.43/0.61  thf('57', plain,
% 0.43/0.61      (![X1 : $i]:
% 0.43/0.61         (((X1) = (sk_C)) | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ sk_C)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['56'])).
% 0.43/0.61  thf('58', plain, (((sk_B_1 @ sk_A) = (sk_C))),
% 0.43/0.61      inference('sup-', [status(thm)], ['50', '57'])).
% 0.43/0.61  thf('59', plain,
% 0.43/0.61      (![X17 : $i]:
% 0.43/0.61         (~ (v1_xboole_0 @ (sk_B_1 @ X17))
% 0.43/0.61          | ~ (l1_pre_topc @ X17)
% 0.43/0.61          | ~ (v2_pre_topc @ X17)
% 0.43/0.61          | (v2_struct_0 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.43/0.61  thf('60', plain,
% 0.43/0.61      ((~ (v1_xboole_0 @ sk_C)
% 0.43/0.61        | (v2_struct_0 @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['58', '59'])).
% 0.43/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.43/0.61  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.43/0.61  thf('62', plain, (((sk_C) = (k1_xboole_0))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('63', plain, ((v1_xboole_0 @ sk_C)),
% 0.43/0.61      inference('demod', [status(thm)], ['61', '62'])).
% 0.43/0.61  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('66', plain, ((v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['60', '63', '64', '65'])).
% 0.43/0.61  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
