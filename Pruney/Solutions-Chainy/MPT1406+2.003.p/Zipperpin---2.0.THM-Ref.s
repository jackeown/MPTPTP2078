%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CxmoI0O27w

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:18 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   58 (  89 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  390 ( 887 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t36_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_connsp_2 @ C @ A @ B )
             => ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m2_connsp_2 @ C @ A @ B )
               => ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_connsp_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m2_connsp_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m2_connsp_2 @ X17 @ X16 @ X15 )
      | ( r1_tarski @ X15 @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m2_connsp_2 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_connsp_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','13'])).

thf('15',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    m2_connsp_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X14 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X5 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('27',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    m1_subset_1 @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CxmoI0O27w
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 254 iterations in 0.183s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.64  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.47/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.64  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.47/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.64  thf(t36_connsp_2, conjecture,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.64           ( ![C:$i]: ( ( m2_connsp_2 @ C @ A @ B ) => ( r1_tarski @ B @ C ) ) ) ) ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i]:
% 0.47/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.64            ( l1_pre_topc @ A ) ) =>
% 0.47/0.64          ( ![B:$i]:
% 0.47/0.64            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.64              ( ![C:$i]:
% 0.47/0.64                ( ( m2_connsp_2 @ C @ A @ B ) => ( r1_tarski @ B @ C ) ) ) ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t36_connsp_2])).
% 0.47/0.64  thf('0', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('1', plain, ((m2_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('2', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(d2_connsp_2, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.64           ( ![C:$i]:
% 0.47/0.64             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.64               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.47/0.64                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.47/0.64  thf('3', plain,
% 0.47/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.47/0.64          | ~ (m2_connsp_2 @ X17 @ X16 @ X15)
% 0.47/0.64          | (r1_tarski @ X15 @ (k1_tops_1 @ X16 @ X17))
% 0.47/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.47/0.64          | ~ (l1_pre_topc @ X16)
% 0.47/0.64          | ~ (v2_pre_topc @ X16))),
% 0.47/0.64      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.47/0.64  thf('4', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v2_pre_topc @ sk_A)
% 0.47/0.64          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.64          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.47/0.64          | ~ (m2_connsp_2 @ X0 @ sk_A @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.64  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('7', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.64          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.47/0.64          | ~ (m2_connsp_2 @ X0 @ sk_A @ sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.47/0.64  thf('8', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(dt_m2_connsp_2, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.47/0.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.64       ( ![C:$i]:
% 0.47/0.64         ( ( m2_connsp_2 @ C @ A @ B ) =>
% 0.47/0.64           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.47/0.64  thf('9', plain,
% 0.47/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X18)
% 0.47/0.64          | ~ (v2_pre_topc @ X18)
% 0.47/0.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.47/0.64          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.47/0.64          | ~ (m2_connsp_2 @ X20 @ X18 @ X19))),
% 0.47/0.64      inference('cnf', [status(esa)], [dt_m2_connsp_2])).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.47/0.64          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.64          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.64          | ~ (l1_pre_topc @ sk_A))),
% 0.47/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.64  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('13', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.47/0.64          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.64      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.47/0.64  thf('14', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.47/0.64          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0)))),
% 0.47/0.64      inference('clc', [status(thm)], ['7', '13'])).
% 0.47/0.64  thf('15', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['1', '14'])).
% 0.47/0.64  thf(d1_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.47/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.47/0.64  thf('16', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         (~ (r1_tarski @ X0 @ X1)
% 0.47/0.64          | (r2_hidden @ X0 @ X2)
% 0.47/0.64          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.47/0.64      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.47/0.64  thf('17', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.47/0.64      inference('simplify', [status(thm)], ['16'])).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['15', '17'])).
% 0.47/0.64  thf('19', plain, ((m2_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('20', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.47/0.64          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.47/0.64      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.47/0.64  thf('21', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.64  thf(t44_tops_1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( l1_pre_topc @ A ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.64           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.47/0.64  thf('22', plain,
% 0.47/0.64      (![X13 : $i, X14 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.47/0.64          | (r1_tarski @ (k1_tops_1 @ X14 @ X13) @ X13)
% 0.47/0.64          | ~ (l1_pre_topc @ X14))),
% 0.47/0.64      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.47/0.64  thf('23', plain,
% 0.47/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.64        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.64  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('25', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.47/0.64      inference('demod', [status(thm)], ['23', '24'])).
% 0.47/0.64  thf(t79_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( r1_tarski @ A @ B ) =>
% 0.47/0.64       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.47/0.64  thf('26', plain,
% 0.47/0.64      (![X5 : $i, X6 : $i]:
% 0.47/0.64         ((r1_tarski @ (k1_zfmisc_1 @ X5) @ (k1_zfmisc_1 @ X6))
% 0.47/0.64          | ~ (r1_tarski @ X5 @ X6))),
% 0.47/0.64      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.47/0.64  thf('27', plain,
% 0.47/0.64      ((r1_tarski @ (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ 
% 0.47/0.64        (k1_zfmisc_1 @ sk_C_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.64  thf(t3_subset, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.64  thf('28', plain,
% 0.47/0.64      (![X7 : $i, X9 : $i]:
% 0.47/0.64         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.47/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.64  thf('29', plain,
% 0.47/0.64      ((m1_subset_1 @ (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C_1)) @ 
% 0.47/0.64        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_C_1)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.64  thf(t4_subset, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.47/0.64       ( m1_subset_1 @ A @ C ) ))).
% 0.47/0.64  thf('30', plain,
% 0.47/0.64      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X10 @ X11)
% 0.47/0.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.47/0.64          | (m1_subset_1 @ X10 @ X12))),
% 0.47/0.64      inference('cnf', [status(esa)], [t4_subset])).
% 0.47/0.64  thf('31', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_C_1))
% 0.47/0.64          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.64  thf('32', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_C_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['18', '31'])).
% 0.47/0.64  thf('33', plain,
% 0.47/0.64      (![X7 : $i, X8 : $i]:
% 0.47/0.64         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.64  thf('34', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.47/0.64      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.64  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
