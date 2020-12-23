%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SaxKs3IBmA

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:02 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 130 expanded)
%              Number of leaves         :   38 (  54 expanded)
%              Depth                    :   19
%              Number of atoms          :  611 (1571 expanded)
%              Number of equality atoms :   14 (  41 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
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

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v4_pre_topc @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v4_pre_topc @ X21 @ X22 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = ( k3_subset_1 @ X4 @ ( k1_subset_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('14',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('15',plain,(
    ! [X4: $i] :
      ( X4
      = ( k3_subset_1 @ X4 @ ( k1_subset_1 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('20',plain,(
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

thf('21',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('22',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('23',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('24',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X23: $i] :
      ( ~ ( v3_pre_topc @ X23 @ sk_A )
      | ~ ( v4_pre_topc @ X23 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X23 )
      | ( r2_hidden @ X23 @ sk_C )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X23: $i] :
      ( ~ ( v3_pre_topc @ X23 @ sk_A )
      | ~ ( v4_pre_topc @ X23 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X23 )
      | ( r2_hidden @ X23 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('31',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('32',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','41'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('46',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_xboole_0 @ ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SaxKs3IBmA
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 237 iterations in 0.100s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.38/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.38/0.56  thf(t28_connsp_2, conjecture,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( m1_subset_1 @
% 0.38/0.56                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.56               ( ~( ( ![D:$i]:
% 0.38/0.56                      ( ( m1_subset_1 @
% 0.38/0.56                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56                        ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.56                          ( ( v3_pre_topc @ D @ A ) & 
% 0.38/0.56                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.38/0.56                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i]:
% 0.38/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.56            ( l1_pre_topc @ A ) ) =>
% 0.38/0.56          ( ![B:$i]:
% 0.38/0.56            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.56              ( ![C:$i]:
% 0.38/0.56                ( ( m1_subset_1 @
% 0.38/0.56                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.56                  ( ~( ( ![D:$i]:
% 0.38/0.56                         ( ( m1_subset_1 @
% 0.38/0.56                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56                           ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.56                             ( ( v3_pre_topc @ D @ A ) & 
% 0.38/0.56                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.38/0.56                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.38/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t2_subset, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.38/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i]:
% 0.38/0.56         ((r2_hidden @ X8 @ X9)
% 0.38/0.56          | (v1_xboole_0 @ X9)
% 0.38/0.56          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf(t4_subset_1, axiom,
% 0.38/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.38/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.56  thf(cc2_pre_topc, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X15 : $i, X16 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.56          | (v4_pre_topc @ X15 @ X16)
% 0.38/0.56          | ~ (v1_xboole_0 @ X15)
% 0.38/0.56          | ~ (l1_pre_topc @ X16)
% 0.38/0.56          | ~ (v2_pre_topc @ X16))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v2_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.56          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.56  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v2_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.38/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.56  thf(t29_tops_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_pre_topc @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56           ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.56             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X21 : $i, X22 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.56          | ~ (v4_pre_topc @ X21 @ X22)
% 0.38/0.56          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21) @ X22)
% 0.38/0.56          | ~ (l1_pre_topc @ X22))),
% 0.38/0.56      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ 
% 0.38/0.56             X0)
% 0.38/0.56          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.56  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.56  thf('12', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.38/0.56  thf(t22_subset_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X4 : $i]:
% 0.38/0.56         ((k2_subset_1 @ X4) = (k3_subset_1 @ X4 @ (k1_subset_1 @ X4)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.38/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.38/0.56  thf('14', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X4 : $i]: ((X4) = (k3_subset_1 @ X4 @ (k1_subset_1 @ X4)))),
% 0.38/0.56      inference('demod', [status(thm)], ['13', '14'])).
% 0.38/0.56  thf('16', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['12', '15'])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['11', '16'])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (v2_pre_topc @ X0)
% 0.38/0.56          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['8', '17'])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (v2_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.56  thf(fc4_pre_topc, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X19 : $i]:
% 0.38/0.56         ((v4_pre_topc @ (k2_struct_0 @ X19) @ X19)
% 0.38/0.56          | ~ (l1_pre_topc @ X19)
% 0.38/0.56          | ~ (v2_pre_topc @ X19))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.38/0.56  thf(d3_struct_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (![X17 : $i]:
% 0.38/0.56         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.56  thf(dt_k2_subset_1, axiom,
% 0.38/0.56    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.38/0.56  thf('23', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.56  thf('24', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.38/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (![X23 : $i]:
% 0.38/0.56         (~ (v3_pre_topc @ X23 @ sk_A)
% 0.38/0.56          | ~ (v4_pre_topc @ X23 @ sk_A)
% 0.38/0.56          | ~ (r2_hidden @ sk_B_1 @ X23)
% 0.38/0.56          | (r2_hidden @ X23 @ sk_C)
% 0.38/0.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('26', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (![X23 : $i]:
% 0.38/0.56         (~ (v3_pre_topc @ X23 @ sk_A)
% 0.38/0.56          | ~ (v4_pre_topc @ X23 @ sk_A)
% 0.38/0.56          | ~ (r2_hidden @ sk_B_1 @ X23)
% 0.38/0.56          | (r2_hidden @ X23 @ k1_xboole_0)
% 0.38/0.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.38/0.56        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.38/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['24', '27'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.38/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.38/0.56        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['21', '28'])).
% 0.38/0.56  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(dt_l1_pre_topc, axiom,
% 0.38/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.38/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.38/0.56        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['29', '32'])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.38/0.56        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['20', '33'])).
% 0.38/0.56  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.38/0.56        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['19', '37'])).
% 0.38/0.56  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      ((~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.38/0.56  thf('42', plain,
% 0.38/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['3', '41'])).
% 0.38/0.56  thf(t7_ordinal1, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 0.38/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.56        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.56  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.56  thf('46', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['44', '45'])).
% 0.38/0.56  thf(rc7_pre_topc, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ?[B:$i]:
% 0.38/0.56         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.56           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.56  thf('47', plain,
% 0.38/0.56      (![X20 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (sk_B @ X20) @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.56          | ~ (l1_pre_topc @ X20)
% 0.38/0.56          | ~ (v2_pre_topc @ X20)
% 0.38/0.56          | (v2_struct_0 @ X20))),
% 0.38/0.56      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.38/0.56  thf(cc1_subset_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_xboole_0 @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.38/0.56          | (v1_xboole_0 @ X6)
% 0.38/0.56          | ~ (v1_xboole_0 @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v2_struct_0 @ X0)
% 0.38/0.56          | ~ (v2_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.38/0.56          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.56  thf('50', plain,
% 0.38/0.56      (((v1_xboole_0 @ (sk_B @ sk_A))
% 0.38/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | (v2_struct_0 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['46', '49'])).
% 0.38/0.56  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('53', plain, (((v1_xboole_0 @ (sk_B @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.38/0.56  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('55', plain, ((v1_xboole_0 @ (sk_B @ sk_A))),
% 0.38/0.56      inference('clc', [status(thm)], ['53', '54'])).
% 0.38/0.56  thf('56', plain,
% 0.38/0.56      (![X20 : $i]:
% 0.38/0.56         (~ (v1_xboole_0 @ (sk_B @ X20))
% 0.38/0.56          | ~ (l1_pre_topc @ X20)
% 0.38/0.56          | ~ (v2_pre_topc @ X20)
% 0.38/0.56          | (v2_struct_0 @ X20))),
% 0.38/0.56      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.38/0.56  thf('57', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.38/0.56  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('60', plain, ((v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.38/0.56  thf('61', plain, ($false), inference('demod', [status(thm)], ['0', '60'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
