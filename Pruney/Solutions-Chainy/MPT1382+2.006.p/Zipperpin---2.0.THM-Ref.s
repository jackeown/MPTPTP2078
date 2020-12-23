%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xs0TWceCwE

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:50 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 158 expanded)
%              Number of leaves         :   24 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  617 (2842 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t7_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( m1_connsp_2 @ C @ A @ B )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( m1_connsp_2 @ D @ A @ B )
                          & ( v3_pre_topc @ D @ A )
                          & ( r1_tarski @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( m1_connsp_2 @ C @ A @ B )
                    & ! [D: $i] :
                        ( ( ~ ( v1_xboole_0 @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                       => ~ ( ( m1_connsp_2 @ D @ A @ B )
                            & ( v3_pre_topc @ D @ A )
                            & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_connsp_2])).

thf('0',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ( r2_hidden @ X15 @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X21: $i] :
      ( ~ ( r1_tarski @ X21 @ sk_C )
      | ~ ( v3_pre_topc @ X21 @ sk_A )
      | ~ ( m1_connsp_2 @ X21 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X14 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X11 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('34',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','37'])).

thf('39',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('40',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( r2_hidden @ X20 @ X18 )
      | ( m1_connsp_2 @ X18 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['38','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['18','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xs0TWceCwE
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:53:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 118 iterations in 0.079s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.35/0.55  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.35/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.55  thf(t7_connsp_2, conjecture,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.35/0.55                    ( ![D:$i]:
% 0.35/0.55                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.35/0.55                          ( m1_subset_1 @
% 0.35/0.55                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.55                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.35/0.55                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i]:
% 0.35/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.55            ( l1_pre_topc @ A ) ) =>
% 0.35/0.55          ( ![B:$i]:
% 0.35/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55              ( ![C:$i]:
% 0.35/0.55                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55                  ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.35/0.55                       ( ![D:$i]:
% 0.35/0.55                         ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.35/0.55                             ( m1_subset_1 @
% 0.35/0.55                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.55                           ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.35/0.55                                ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t7_connsp_2])).
% 0.35/0.55  thf('0', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(d1_connsp_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.35/0.55                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.35/0.55          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 0.35/0.55          | (r2_hidden @ X15 @ (k1_tops_1 @ X16 @ X17))
% 0.35/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.35/0.55          | ~ (l1_pre_topc @ X16)
% 0.35/0.55          | ~ (v2_pre_topc @ X16)
% 0.35/0.55          | (v2_struct_0 @ X16))),
% 0.35/0.55      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.55  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('6', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.35/0.55  thf('7', plain,
% 0.35/0.55      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55        | (v2_struct_0 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['0', '6'])).
% 0.35/0.55  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('9', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.35/0.55  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('11', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.35/0.55      inference('clc', [status(thm)], ['9', '10'])).
% 0.35/0.55  thf(d10_xboole_0, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.35/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.55  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.35/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.35/0.55  thf(t3_subset, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.55  thf('14', plain,
% 0.35/0.55      (![X3 : $i, X5 : $i]:
% 0.35/0.55         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.35/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.55  thf('15', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.55  thf(t5_subset, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.35/0.55          ( v1_xboole_0 @ C ) ) ))).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X6 @ X7)
% 0.35/0.55          | ~ (v1_xboole_0 @ X8)
% 0.35/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.35/0.55      inference('cnf', [status(esa)], [t5_subset])).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.55  thf('18', plain, (~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['11', '17'])).
% 0.35/0.55  thf('19', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(dt_k1_tops_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( l1_pre_topc @ A ) & 
% 0.35/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.55       ( m1_subset_1 @
% 0.35/0.55         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.55  thf('20', plain,
% 0.35/0.55      (![X9 : $i, X10 : $i]:
% 0.35/0.55         (~ (l1_pre_topc @ X9)
% 0.35/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.35/0.55          | (m1_subset_1 @ (k1_tops_1 @ X9 @ X10) @ 
% 0.35/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.35/0.55  thf('21', plain,
% 0.35/0.55      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.35/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.55  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('23', plain,
% 0.35/0.55      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.35/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.35/0.55  thf('24', plain,
% 0.35/0.55      (![X21 : $i]:
% 0.35/0.55         (~ (r1_tarski @ X21 @ sk_C)
% 0.35/0.55          | ~ (v3_pre_topc @ X21 @ sk_A)
% 0.35/0.55          | ~ (m1_connsp_2 @ X21 @ sk_A @ sk_B)
% 0.35/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55          | (v1_xboole_0 @ X21))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('25', plain,
% 0.35/0.55      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B)
% 0.35/0.55        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.35/0.55        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t44_tops_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( l1_pre_topc @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.35/0.55  thf('27', plain,
% 0.35/0.55      (![X13 : $i, X14 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.35/0.55          | (r1_tarski @ (k1_tops_1 @ X14 @ X13) @ X13)
% 0.35/0.55          | ~ (l1_pre_topc @ X14))),
% 0.35/0.55      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.35/0.55  thf('28', plain,
% 0.35/0.55      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.55  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('30', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.35/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.35/0.55  thf('31', plain,
% 0.35/0.55      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B)
% 0.35/0.55        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['25', '30'])).
% 0.35/0.55  thf('32', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(fc9_tops_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.35/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.55       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.35/0.55  thf('33', plain,
% 0.35/0.55      (![X11 : $i, X12 : $i]:
% 0.35/0.55         (~ (l1_pre_topc @ X11)
% 0.35/0.55          | ~ (v2_pre_topc @ X11)
% 0.35/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.35/0.55          | (v3_pre_topc @ (k1_tops_1 @ X11 @ X12) @ X11))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.35/0.55  thf('34', plain,
% 0.35/0.55      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.35/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.55  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('37', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.35/0.55      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.35/0.55  thf('38', plain,
% 0.35/0.55      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B))),
% 0.35/0.55      inference('demod', [status(thm)], ['31', '37'])).
% 0.35/0.55  thf('39', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.35/0.55      inference('clc', [status(thm)], ['9', '10'])).
% 0.35/0.55  thf('40', plain,
% 0.35/0.55      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.35/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.35/0.55  thf(t5_connsp_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.35/0.55                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.35/0.55  thf('41', plain,
% 0.35/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.35/0.55          | ~ (v3_pre_topc @ X18 @ X19)
% 0.35/0.55          | ~ (r2_hidden @ X20 @ X18)
% 0.35/0.55          | (m1_connsp_2 @ X18 @ X19 @ X20)
% 0.35/0.55          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.35/0.55          | ~ (l1_pre_topc @ X19)
% 0.35/0.55          | ~ (v2_pre_topc @ X19)
% 0.35/0.55          | (v2_struct_0 @ X19))),
% 0.35/0.55      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.35/0.55  thf('42', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ X0)
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.55          | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.35/0.55  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('45', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.35/0.55      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.35/0.55  thf('46', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ X0)
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.35/0.55      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.35/0.55  thf('47', plain,
% 0.35/0.55      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B)
% 0.35/0.55        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | (v2_struct_0 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['39', '46'])).
% 0.35/0.55  thf('48', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('49', plain,
% 0.35/0.55      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B)
% 0.35/0.55        | (v2_struct_0 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.35/0.55  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('51', plain, ((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A @ sk_B)),
% 0.35/0.55      inference('clc', [status(thm)], ['49', '50'])).
% 0.35/0.55  thf('52', plain, ((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['38', '51'])).
% 0.35/0.55  thf('53', plain, ($false), inference('demod', [status(thm)], ['18', '52'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.35/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
