%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OlBWVKZYcA

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:03 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 149 expanded)
%              Number of leaves         :   39 (  60 expanded)
%              Depth                    :   20
%              Number of atoms          :  639 (1625 expanded)
%              Number of equality atoms :   21 (  52 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(cc2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v2_tops_1 @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_tops_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v2_tops_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tops_1 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_tops_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(fc14_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ~ ( v2_tops_1 @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('8',plain,(
    ! [X23: $i] :
      ( ~ ( v2_tops_1 @ ( k2_struct_0 @ X23 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc14_tops_1])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('19',plain,(
    ! [X18: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('20',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('22',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('23',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X24: $i] :
      ( ~ ( v3_pre_topc @ X24 @ sk_A )
      | ~ ( v4_pre_topc @ X24 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X24 )
      | ( r2_hidden @ X24 @ sk_C )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X24: $i] :
      ( ~ ( v3_pre_topc @ X24 @ sk_A )
      | ~ ( v4_pre_topc @ X24 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X24 )
      | ( r2_hidden @ X24 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v4_pre_topc @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('37',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v4_pre_topc @ X21 @ X22 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('39',plain,(
    ! [X2: $i] :
      ( ( k1_subset_1 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = ( k3_subset_1 @ X5 @ ( k1_subset_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('41',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('42',plain,(
    ! [X5: $i] :
      ( X5
      = ( k3_subset_1 @ X5 @ ( k1_subset_1 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['27','48'])).

thf('50',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('52',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('53',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','58'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('60',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('62',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('63',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('68',plain,
    ( ( k2_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['14','68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OlBWVKZYcA
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 254 iterations in 0.125s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.38/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.38/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.38/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.38/0.57  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.38/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.38/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.38/0.57  thf(t28_connsp_2, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.57           ( ![C:$i]:
% 0.38/0.57             ( ( m1_subset_1 @
% 0.38/0.57                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.57               ( ~( ( ![D:$i]:
% 0.38/0.57                      ( ( m1_subset_1 @
% 0.38/0.57                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57                        ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.57                          ( ( v3_pre_topc @ D @ A ) & 
% 0.38/0.57                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.38/0.57                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.57            ( l1_pre_topc @ A ) ) =>
% 0.38/0.57          ( ![B:$i]:
% 0.38/0.57            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.57              ( ![C:$i]:
% 0.38/0.57                ( ( m1_subset_1 @
% 0.38/0.57                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.57                  ( ~( ( ![D:$i]:
% 0.38/0.57                         ( ( m1_subset_1 @
% 0.38/0.57                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57                           ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.57                             ( ( v3_pre_topc @ D @ A ) & 
% 0.38/0.57                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.38/0.57                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.38/0.57  thf('0', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(l13_xboole_0, axiom,
% 0.38/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf(t4_subset_1, axiom,
% 0.38/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['1', '2'])).
% 0.38/0.57  thf(cc2_tops_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( v1_xboole_0 @ B ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.38/0.57          | (v2_tops_1 @ X19 @ X20)
% 0.38/0.57          | ~ (v1_xboole_0 @ X19)
% 0.38/0.57          | ~ (l1_pre_topc @ X20))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc2_tops_1])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (v1_xboole_0 @ X1)
% 0.38/0.57          | ~ (l1_pre_topc @ X0)
% 0.38/0.57          | ~ (v1_xboole_0 @ X1)
% 0.38/0.57          | (v2_tops_1 @ X1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((v2_tops_1 @ X1 @ X0) | ~ (l1_pre_topc @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.57      inference('simplify', [status(thm)], ['5'])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v2_tops_1 @ X0 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '6'])).
% 0.38/0.57  thf(fc14_tops_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ~( v2_tops_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X23 : $i]:
% 0.38/0.57         (~ (v2_tops_1 @ (k2_struct_0 @ X23) @ X23)
% 0.38/0.57          | ~ (l1_pre_topc @ X23)
% 0.38/0.57          | ~ (v2_pre_topc @ X23)
% 0.38/0.57          | (v2_struct_0 @ X23))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc14_tops_1])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf('10', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.38/0.57  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('14', plain, (~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.38/0.57      inference('clc', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf(d3_struct_0, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X16 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t2_subset, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.38/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X7 : $i, X8 : $i]:
% 0.38/0.57         ((r2_hidden @ X7 @ X8)
% 0.38/0.57          | (v1_xboole_0 @ X8)
% 0.38/0.57          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.38/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.57  thf(fc4_pre_topc, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X18 : $i]:
% 0.38/0.57         ((v4_pre_topc @ (k2_struct_0 @ X18) @ X18)
% 0.38/0.57          | ~ (l1_pre_topc @ X18)
% 0.38/0.57          | ~ (v2_pre_topc @ X18))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X16 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf(dt_k2_subset_1, axiom,
% 0.38/0.57    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.38/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.38/0.57  thf('22', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.57  thf('23', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.38/0.57      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (![X24 : $i]:
% 0.38/0.57         (~ (v3_pre_topc @ X24 @ sk_A)
% 0.38/0.57          | ~ (v4_pre_topc @ X24 @ sk_A)
% 0.38/0.57          | ~ (r2_hidden @ sk_B @ X24)
% 0.38/0.57          | (r2_hidden @ X24 @ sk_C)
% 0.38/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('25', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X24 : $i]:
% 0.38/0.57         (~ (v3_pre_topc @ X24 @ sk_A)
% 0.38/0.57          | ~ (v4_pre_topc @ X24 @ sk_A)
% 0.38/0.57          | ~ (r2_hidden @ sk_B @ X24)
% 0.38/0.57          | (r2_hidden @ X24 @ k1_xboole_0)
% 0.38/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.38/0.57        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.38/0.57        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['23', '26'])).
% 0.38/0.57  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['1', '2'])).
% 0.38/0.57  thf(cc2_pre_topc, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.38/0.57          | (v4_pre_topc @ X14 @ X15)
% 0.38/0.57          | ~ (v1_xboole_0 @ X14)
% 0.38/0.57          | ~ (l1_pre_topc @ X15)
% 0.38/0.57          | ~ (v2_pre_topc @ X15))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (v1_xboole_0 @ X1)
% 0.38/0.57          | ~ (v2_pre_topc @ X0)
% 0.38/0.57          | ~ (l1_pre_topc @ X0)
% 0.38/0.57          | ~ (v1_xboole_0 @ X1)
% 0.38/0.57          | (v4_pre_topc @ X1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((v4_pre_topc @ X1 @ X0)
% 0.38/0.57          | ~ (l1_pre_topc @ X0)
% 0.38/0.57          | ~ (v2_pre_topc @ X0)
% 0.38/0.57          | ~ (v1_xboole_0 @ X1))),
% 0.38/0.57      inference('simplify', [status(thm)], ['31'])).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_xboole_0 @ X0)
% 0.38/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.57          | (v4_pre_topc @ X0 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['28', '32'])).
% 0.38/0.57  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.57  thf(t29_tops_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57           ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.57             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      (![X21 : $i, X22 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.38/0.57          | ~ (v4_pre_topc @ X21 @ X22)
% 0.38/0.57          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21) @ X22)
% 0.38/0.57          | ~ (l1_pre_topc @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ X0)
% 0.38/0.57          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ 
% 0.38/0.57             X0)
% 0.38/0.57          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.57  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.57  thf('39', plain, (![X2 : $i]: ((k1_subset_1 @ X2) = (k1_xboole_0))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.38/0.57  thf(t22_subset_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (![X5 : $i]:
% 0.38/0.57         ((k2_subset_1 @ X5) = (k3_subset_1 @ X5 @ (k1_subset_1 @ X5)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.38/0.57  thf('41', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      (![X5 : $i]: ((X5) = (k3_subset_1 @ X5 @ (k1_subset_1 @ X5)))),
% 0.38/0.57      inference('demod', [status(thm)], ['40', '41'])).
% 0.38/0.57  thf('43', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['39', '42'])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ X0)
% 0.38/0.57          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.38/0.57          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.38/0.57      inference('demod', [status(thm)], ['38', '43'])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.57        | (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['35', '44'])).
% 0.38/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.57  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.57  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('48', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.38/0.57      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.38/0.57        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['27', '48'])).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.57        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['20', '49'])).
% 0.38/0.57  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(dt_l1_pre_topc, axiom,
% 0.38/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.57  thf('52', plain,
% 0.38/0.57      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('53', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.57  thf('54', plain,
% 0.38/0.57      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.38/0.57        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.38/0.57      inference('demod', [status(thm)], ['50', '53'])).
% 0.38/0.57  thf('55', plain,
% 0.38/0.57      ((~ (v2_pre_topc @ sk_A)
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.38/0.57        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '54'])).
% 0.38/0.57  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('58', plain,
% 0.38/0.57      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.38/0.57        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.38/0.57  thf('59', plain,
% 0.38/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['18', '58'])).
% 0.38/0.57  thf(t7_ordinal1, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.57  thf('60', plain,
% 0.38/0.57      (![X12 : $i, X13 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.38/0.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.57  thf('61', plain,
% 0.38/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.57  thf('62', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.38/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.57  thf('63', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['61', '62'])).
% 0.38/0.57  thf('64', plain,
% 0.38/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.57  thf('65', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.57  thf('66', plain,
% 0.38/0.57      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup+', [status(thm)], ['15', '65'])).
% 0.38/0.57  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.57  thf('68', plain, (((k2_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.38/0.57      inference('demod', [status(thm)], ['66', '67'])).
% 0.38/0.57  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.57  thf('70', plain, ($false),
% 0.38/0.57      inference('demod', [status(thm)], ['14', '68', '69'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
