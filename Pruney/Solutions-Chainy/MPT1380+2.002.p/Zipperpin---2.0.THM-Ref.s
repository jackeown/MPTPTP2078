%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tUe95IfSop

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  79 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  375 ( 984 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t5_connsp_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( ( v3_pre_topc @ B @ A )
                    & ( r2_hidden @ C @ B ) )
                 => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ ( k1_tops_1 @ X9 @ X10 ) )
      | ( m1_connsp_2 @ X10 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X4 @ X3 ) @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v3_pre_topc @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k1_tops_1 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','24'])).

thf('26',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ( m1_connsp_2 @ sk_B @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_connsp_2 @ sk_B @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( m1_connsp_2 @ sk_B @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tUe95IfSop
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 18:13:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 27 iterations in 0.015s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.46  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.46  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(t5_connsp_2, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46           ( ![C:$i]:
% 0.20/0.46             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.46               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.20/0.46                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.46            ( l1_pre_topc @ A ) ) =>
% 0.20/0.46          ( ![B:$i]:
% 0.20/0.46            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46              ( ![C:$i]:
% 0.20/0.46                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.46                  ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.20/0.46                    ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t5_connsp_2])).
% 0.20/0.46  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d1_connsp_2, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.46           ( ![C:$i]:
% 0.20/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.46                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.20/0.46          | ~ (r2_hidden @ X8 @ (k1_tops_1 @ X9 @ X10))
% 0.20/0.46          | (m1_connsp_2 @ X10 @ X9 @ X8)
% 0.20/0.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.46          | ~ (l1_pre_topc @ X9)
% 0.20/0.46          | ~ (v2_pre_topc @ X9)
% 0.20/0.46          | (v2_struct_0 @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v2_struct_0 @ sk_A)
% 0.20/0.46          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.46          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.46          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 0.20/0.46          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v2_struct_0 @ sk_A)
% 0.20/0.46          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 0.20/0.46          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t44_tops_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( l1_pre_topc @ A ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.46          | (r1_tarski @ (k1_tops_1 @ X4 @ X3) @ X3)
% 0.20/0.46          | ~ (l1_pre_topc @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.46  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.46      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf(d10_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X0 : $i, X2 : $i]:
% 0.20/0.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.20/0.46        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t56_tops_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( l1_pre_topc @ A ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46           ( ![C:$i]:
% 0.20/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.46               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.46                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.46          | ~ (v3_pre_topc @ X5 @ X6)
% 0.20/0.46          | ~ (r1_tarski @ X5 @ X7)
% 0.20/0.46          | (r1_tarski @ X5 @ (k1_tops_1 @ X6 @ X7))
% 0.20/0.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.46          | ~ (l1_pre_topc @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (l1_pre_topc @ sk_A)
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.46          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.46          | ~ (r1_tarski @ sk_B @ X0)
% 0.20/0.46          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.46  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('20', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.46          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.46          | ~ (r1_tarski @ sk_B @ X0))),
% 0.20/0.46      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      ((~ (r1_tarski @ sk_B @ sk_B)
% 0.20/0.46        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['15', '21'])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.46  thf('24', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.46      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.46  thf('25', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['22', '24'])).
% 0.20/0.46  thf('26', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['14', '25'])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((v2_struct_0 @ sk_A)
% 0.20/0.46          | (m1_connsp_2 @ sk_B @ sk_A @ X0)
% 0.20/0.46          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.46      inference('demod', [status(thm)], ['7', '26'])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      ((~ (r2_hidden @ sk_C @ sk_B)
% 0.20/0.46        | (m1_connsp_2 @ sk_B @ sk_A @ sk_C)
% 0.20/0.46        | (v2_struct_0 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '27'])).
% 0.20/0.46  thf('29', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      (((m1_connsp_2 @ sk_B @ sk_A @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.46  thf('31', plain, (~ (m1_connsp_2 @ sk_B @ sk_A @ sk_C)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('32', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.46      inference('clc', [status(thm)], ['30', '31'])).
% 0.20/0.46  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
