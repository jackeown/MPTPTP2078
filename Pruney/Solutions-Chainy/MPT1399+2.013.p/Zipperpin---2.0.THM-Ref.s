%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rMAe0nvFOj

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 112 expanded)
%              Number of leaves         :   36 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  533 (1199 expanded)
%              Number of equality atoms :   14 (  33 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v4_pre_topc @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v4_pre_topc @ X19 @ X20 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ! [X18: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('21',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
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
    ! [X21: $i] :
      ( ~ ( v3_pre_topc @ X21 @ sk_A )
      | ~ ( v4_pre_topc @ X21 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X21 )
      | ( r2_hidden @ X21 @ sk_C )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X21: $i] :
      ( ~ ( v3_pre_topc @ X21 @ sk_A )
      | ~ ( v4_pre_topc @ X21 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X21 )
      | ( r2_hidden @ X21 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
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
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('32',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
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
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
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
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
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

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf('50',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rMAe0nvFOj
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:11:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 180 iterations in 0.034s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(t28_connsp_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_subset_1 @
% 0.20/0.47                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47               ( ~( ( ![D:$i]:
% 0.20/0.47                      ( ( m1_subset_1 @
% 0.20/0.47                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47                        ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.47                          ( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.47                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.20/0.47                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47            ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47              ( ![C:$i]:
% 0.20/0.47                ( ( m1_subset_1 @
% 0.20/0.47                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47                  ( ~( ( ![D:$i]:
% 0.20/0.47                         ( ( m1_subset_1 @
% 0.20/0.47                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47                           ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.47                             ( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.47                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.20/0.47                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.20/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t2_subset, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.47       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         ((r2_hidden @ X6 @ X7)
% 0.20/0.47          | (v1_xboole_0 @ X7)
% 0.20/0.47          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf(t4_subset_1, axiom,
% 0.20/0.47    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.47  thf(cc2_pre_topc, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.47          | (v4_pre_topc @ X13 @ X14)
% 0.20/0.47          | ~ (v1_xboole_0 @ X13)
% 0.20/0.47          | ~ (l1_pre_topc @ X14)
% 0.20/0.47          | ~ (v2_pre_topc @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.47          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.47  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.47  thf(t29_tops_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.47             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X19 : $i, X20 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.47          | ~ (v4_pre_topc @ X19 @ X20)
% 0.20/0.47          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.20/0.47          | ~ (l1_pre_topc @ X20))),
% 0.20/0.47      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ 
% 0.20/0.47             X0)
% 0.20/0.47          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.47  thf('12', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.47  thf(t22_subset_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X4 : $i]:
% 0.20/0.47         ((k2_subset_1 @ X4) = (k3_subset_1 @ X4 @ (k1_subset_1 @ X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.20/0.47  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.47  thf('14', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X4 : $i]: ((X4) = (k3_subset_1 @ X4 @ (k1_subset_1 @ X4)))),
% 0.20/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['12', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.47          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.47  thf(fc4_pre_topc, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X18 : $i]:
% 0.20/0.47         ((v4_pre_topc @ (k2_struct_0 @ X18) @ X18)
% 0.20/0.47          | ~ (l1_pre_topc @ X18)
% 0.20/0.47          | ~ (v2_pre_topc @ X18))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.20/0.47  thf(d3_struct_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X15 : $i]:
% 0.20/0.47         (((k2_struct_0 @ X15) = (u1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.47  thf(dt_k2_subset_1, axiom,
% 0.20/0.47    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.47  thf('23', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.47  thf('24', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.20/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X21 : $i]:
% 0.20/0.47         (~ (v3_pre_topc @ X21 @ sk_A)
% 0.20/0.47          | ~ (v4_pre_topc @ X21 @ sk_A)
% 0.20/0.47          | ~ (r2_hidden @ sk_B @ X21)
% 0.20/0.47          | (r2_hidden @ X21 @ sk_C)
% 0.20/0.47          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('26', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X21 : $i]:
% 0.20/0.47         (~ (v3_pre_topc @ X21 @ sk_A)
% 0.20/0.47          | ~ (v4_pre_topc @ X21 @ sk_A)
% 0.20/0.47          | ~ (r2_hidden @ sk_B @ X21)
% 0.20/0.47          | (r2_hidden @ X21 @ k1_xboole_0)
% 0.20/0.47          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.20/0.47        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.20/0.47        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.20/0.47        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.20/0.47        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '28'])).
% 0.20/0.47  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_l1_pre_topc, axiom,
% 0.20/0.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.47  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.20/0.47        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.20/0.47        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['29', '32'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.20/0.47        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['20', '33'])).
% 0.20/0.47  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.20/0.47        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['19', '37'])).
% 0.20/0.47  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      ((~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '41'])).
% 0.20/0.47  thf(t7_ordinal1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.47  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.47  thf('46', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.47  thf(fc2_struct_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.47       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      (![X17 : $i]:
% 0.20/0.47         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.20/0.47          | ~ (l1_struct_0 @ X17)
% 0.20/0.47          | (v2_struct_0 @ X17))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.47  thf('48', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.47  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.47  thf('50', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.47  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
