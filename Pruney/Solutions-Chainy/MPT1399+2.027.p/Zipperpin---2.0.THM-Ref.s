%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Rn8hW0tIhf

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:06 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 106 expanded)
%              Number of leaves         :   32 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  472 (1215 expanded)
%              Number of equality atoms :    9 (  29 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('7',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('10',plain,(
    ! [X17: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('11',plain,(
    ! [X16: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('13',plain,(
    ! [X20: $i] :
      ( ~ ( v3_pre_topc @ X20 @ sk_A )
      | ~ ( v4_pre_topc @ X20 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X20 )
      | ( r2_hidden @ X20 @ sk_C )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X20: $i] :
      ( ~ ( v3_pre_topc @ X20 @ sk_A )
      | ~ ( v4_pre_topc @ X20 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X20 )
      | ( r2_hidden @ X20 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('18',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('31',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_setfam_1 @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t5_tops_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) )
              & ( B = k1_xboole_0 ) ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( m1_setfam_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( X18 != k1_xboole_0 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t5_tops_2])).

thf('38',plain,(
    ! [X19: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_struct_0 @ X19 )
      | ~ ( m1_setfam_1 @ k1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('39',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('40',plain,(
    ! [X19: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_struct_0 @ X19 )
      | ~ ( m1_setfam_1 @ k1_xboole_0 @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('44',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Rn8hW0tIhf
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:02:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.59  % Solved by: fo/fo7.sh
% 0.36/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.59  % done 124 iterations in 0.135s
% 0.36/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.59  % SZS output start Refutation
% 0.36/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.36/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.59  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.36/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.59  thf(t28_connsp_2, conjecture,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.59           ( ![C:$i]:
% 0.36/0.59             ( ( m1_subset_1 @
% 0.36/0.59                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.59               ( ~( ( ![D:$i]:
% 0.36/0.59                      ( ( m1_subset_1 @
% 0.36/0.59                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.59                        ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.59                          ( ( v3_pre_topc @ D @ A ) & 
% 0.36/0.59                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.36/0.59                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.59    (~( ![A:$i]:
% 0.36/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.59            ( l1_pre_topc @ A ) ) =>
% 0.36/0.59          ( ![B:$i]:
% 0.36/0.59            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.59              ( ![C:$i]:
% 0.36/0.59                ( ( m1_subset_1 @
% 0.36/0.59                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.59                  ( ~( ( ![D:$i]:
% 0.36/0.59                         ( ( m1_subset_1 @
% 0.36/0.59                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.59                           ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.59                             ( ( v3_pre_topc @ D @ A ) & 
% 0.36/0.59                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.36/0.59                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.36/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(d3_struct_0, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.36/0.59  thf('1', plain,
% 0.36/0.59      (![X13 : $i]:
% 0.36/0.59         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.36/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.59  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(t2_subset, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.59       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.59  thf('3', plain,
% 0.36/0.59      (![X6 : $i, X7 : $i]:
% 0.36/0.59         ((r2_hidden @ X6 @ X7)
% 0.36/0.59          | (v1_xboole_0 @ X7)
% 0.36/0.59          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.36/0.59      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.59  thf('4', plain,
% 0.36/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.59  thf('5', plain,
% 0.36/0.59      (((r2_hidden @ sk_B @ (k2_struct_0 @ sk_A))
% 0.36/0.59        | ~ (l1_struct_0 @ sk_A)
% 0.36/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['1', '4'])).
% 0.36/0.59  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(dt_l1_pre_topc, axiom,
% 0.36/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.59  thf('7', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.36/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.59  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.59  thf('9', plain,
% 0.36/0.59      (((r2_hidden @ sk_B @ (k2_struct_0 @ sk_A))
% 0.36/0.59        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.59      inference('demod', [status(thm)], ['5', '8'])).
% 0.36/0.59  thf(fc10_tops_1, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.59       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.36/0.59  thf('10', plain,
% 0.36/0.59      (![X17 : $i]:
% 0.36/0.59         ((v3_pre_topc @ (k2_struct_0 @ X17) @ X17)
% 0.36/0.59          | ~ (l1_pre_topc @ X17)
% 0.36/0.59          | ~ (v2_pre_topc @ X17))),
% 0.36/0.59      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.36/0.59  thf(fc4_pre_topc, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.59       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.36/0.59  thf('11', plain,
% 0.36/0.59      (![X16 : $i]:
% 0.36/0.59         ((v4_pre_topc @ (k2_struct_0 @ X16) @ X16)
% 0.36/0.59          | ~ (l1_pre_topc @ X16)
% 0.36/0.59          | ~ (v2_pre_topc @ X16))),
% 0.36/0.59      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.36/0.59  thf(dt_k2_struct_0, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( l1_struct_0 @ A ) =>
% 0.36/0.59       ( m1_subset_1 @
% 0.36/0.59         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.59  thf('12', plain,
% 0.36/0.59      (![X14 : $i]:
% 0.36/0.59         ((m1_subset_1 @ (k2_struct_0 @ X14) @ 
% 0.36/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.36/0.59          | ~ (l1_struct_0 @ X14))),
% 0.36/0.59      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.36/0.59  thf('13', plain,
% 0.36/0.59      (![X20 : $i]:
% 0.36/0.59         (~ (v3_pre_topc @ X20 @ sk_A)
% 0.36/0.59          | ~ (v4_pre_topc @ X20 @ sk_A)
% 0.36/0.59          | ~ (r2_hidden @ sk_B @ X20)
% 0.36/0.59          | (r2_hidden @ X20 @ sk_C)
% 0.36/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('14', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('15', plain,
% 0.36/0.59      (![X20 : $i]:
% 0.36/0.59         (~ (v3_pre_topc @ X20 @ sk_A)
% 0.36/0.59          | ~ (v4_pre_topc @ X20 @ sk_A)
% 0.36/0.59          | ~ (r2_hidden @ sk_B @ X20)
% 0.36/0.59          | (r2_hidden @ X20 @ k1_xboole_0)
% 0.36/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.59  thf('16', plain,
% 0.36/0.59      ((~ (l1_struct_0 @ sk_A)
% 0.36/0.59        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.59        | ~ (r2_hidden @ sk_B @ (k2_struct_0 @ sk_A))
% 0.36/0.59        | ~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.36/0.59        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['12', '15'])).
% 0.36/0.59  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.59  thf('18', plain,
% 0.36/0.59      (((r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.59        | ~ (r2_hidden @ sk_B @ (k2_struct_0 @ sk_A))
% 0.36/0.59        | ~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.36/0.59        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.36/0.59  thf('19', plain,
% 0.36/0.59      ((~ (v2_pre_topc @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.36/0.59        | ~ (r2_hidden @ sk_B @ (k2_struct_0 @ sk_A))
% 0.36/0.59        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['11', '18'])).
% 0.36/0.59  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('22', plain,
% 0.36/0.59      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.36/0.59        | ~ (r2_hidden @ sk_B @ (k2_struct_0 @ sk_A))
% 0.36/0.59        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.59      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.36/0.59  thf('23', plain,
% 0.36/0.59      ((~ (v2_pre_topc @ sk_A)
% 0.36/0.59        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.59        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.59        | ~ (r2_hidden @ sk_B @ (k2_struct_0 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['10', '22'])).
% 0.36/0.59  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('26', plain,
% 0.36/0.59      (((r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.59        | ~ (r2_hidden @ sk_B @ (k2_struct_0 @ sk_A)))),
% 0.36/0.59      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.36/0.59  thf('27', plain,
% 0.36/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['9', '26'])).
% 0.36/0.59  thf(t7_ordinal1, axiom,
% 0.36/0.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.59  thf('28', plain,
% 0.36/0.59      (![X11 : $i, X12 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.36/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.36/0.59  thf('29', plain,
% 0.36/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.59        | ~ (r1_tarski @ k1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.59  thf('30', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.36/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.59  thf('31', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.59      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.59  thf(l13_xboole_0, axiom,
% 0.36/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.59  thf('32', plain,
% 0.36/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.59  thf('33', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.36/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.59  thf('34', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['32', '33'])).
% 0.36/0.59  thf(d12_setfam_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.36/0.59  thf('35', plain,
% 0.36/0.59      (![X3 : $i, X5 : $i]:
% 0.36/0.59         ((m1_setfam_1 @ X5 @ X3) | ~ (r1_tarski @ X3 @ (k3_tarski @ X5)))),
% 0.36/0.59      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.36/0.59  thf('36', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X1) | (m1_setfam_1 @ X0 @ X1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.59  thf(t5_tops_2, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.59       ( ![B:$i]:
% 0.36/0.59         ( ( m1_subset_1 @
% 0.36/0.59             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.59           ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.59                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.59  thf('37', plain,
% 0.36/0.59      (![X18 : $i, X19 : $i]:
% 0.36/0.59         (~ (m1_subset_1 @ X18 @ 
% 0.36/0.59             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 0.36/0.59          | ~ (m1_setfam_1 @ X18 @ (u1_struct_0 @ X19))
% 0.36/0.59          | ((X18) != (k1_xboole_0))
% 0.36/0.59          | ~ (l1_struct_0 @ X19)
% 0.36/0.59          | (v2_struct_0 @ X19))),
% 0.36/0.59      inference('cnf', [status(esa)], [t5_tops_2])).
% 0.36/0.59  thf('38', plain,
% 0.36/0.59      (![X19 : $i]:
% 0.36/0.59         ((v2_struct_0 @ X19)
% 0.36/0.59          | ~ (l1_struct_0 @ X19)
% 0.36/0.59          | ~ (m1_setfam_1 @ k1_xboole_0 @ (u1_struct_0 @ X19))
% 0.36/0.59          | ~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.36/0.59               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))))),
% 0.36/0.59      inference('simplify', [status(thm)], ['37'])).
% 0.36/0.59  thf(t4_subset_1, axiom,
% 0.36/0.59    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.59  thf('39', plain,
% 0.36/0.59      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.36/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.59  thf('40', plain,
% 0.36/0.59      (![X19 : $i]:
% 0.36/0.59         ((v2_struct_0 @ X19)
% 0.36/0.59          | ~ (l1_struct_0 @ X19)
% 0.36/0.59          | ~ (m1_setfam_1 @ k1_xboole_0 @ (u1_struct_0 @ X19)))),
% 0.36/0.59      inference('demod', [status(thm)], ['38', '39'])).
% 0.36/0.59  thf('41', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.36/0.59          | ~ (l1_struct_0 @ X0)
% 0.36/0.59          | (v2_struct_0 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['36', '40'])).
% 0.36/0.59  thf('42', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['31', '41'])).
% 0.36/0.59  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.59  thf('44', plain, ((v2_struct_0 @ sk_A)),
% 0.36/0.59      inference('demod', [status(thm)], ['42', '43'])).
% 0.36/0.59  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
