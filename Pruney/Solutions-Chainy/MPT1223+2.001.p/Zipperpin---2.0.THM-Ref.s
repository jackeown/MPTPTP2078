%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yBzsO1Q8u8

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:44 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   43 (  58 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  348 ( 679 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t31_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( r1_tarski @ C @ B ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v4_pre_topc @ B @ A )
                    & ( r1_tarski @ C @ B ) )
                 => ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t45_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( v4_pre_topc @ D @ A )
                        & ( r1_tarski @ B @ D ) )
                     => ( r2_hidden @ C @ D ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ~ ( v4_pre_topc @ X12 @ X10 )
      | ~ ( r1_tarski @ X9 @ X12 )
      | ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ sk_C_1 @ X1 )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ sk_C_1 @ X1 )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( r1_tarski @ sk_C_1 @ sk_B )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yBzsO1Q8u8
% 0.14/0.37  % Computer   : n007.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 17:36:36 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 95 iterations in 0.072s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.56  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.56  thf(t31_tops_1, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.37/0.56                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( l1_pre_topc @ A ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56              ( ![C:$i]:
% 0.37/0.56                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56                  ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.37/0.56                    ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t31_tops_1])).
% 0.37/0.56  thf('0', plain, (~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_C_1) @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(d3_tarski, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t45_pre_topc, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.37/0.56                 ( ![D:$i]:
% 0.37/0.56                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56                     ( ( ( v4_pre_topc @ D @ A ) & ( r1_tarski @ B @ D ) ) =>
% 0.37/0.56                       ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.37/0.56          | ~ (r2_hidden @ X11 @ (k2_pre_topc @ X10 @ X9))
% 0.37/0.56          | ~ (v4_pre_topc @ X12 @ X10)
% 0.37/0.56          | ~ (r1_tarski @ X9 @ X12)
% 0.37/0.56          | (r2_hidden @ X11 @ X12)
% 0.37/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.37/0.56          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X10))
% 0.37/0.56          | ~ (l1_pre_topc @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t45_pre_topc])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (r2_hidden @ X0 @ X1)
% 0.37/0.56          | ~ (r1_tarski @ sk_C_1 @ X1)
% 0.37/0.56          | ~ (v4_pre_topc @ X1 @ sk_A)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.56  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56          | (r2_hidden @ X0 @ X1)
% 0.37/0.56          | ~ (r1_tarski @ sk_C_1 @ X1)
% 0.37/0.56          | ~ (v4_pre_topc @ X1 @ sk_A)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 0.37/0.56          | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.37/0.56          | ~ (r1_tarski @ sk_C_1 @ sk_B)
% 0.37/0.56          | (r2_hidden @ X0 @ sk_B)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '7'])).
% 0.37/0.56  thf('9', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('10', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 0.37/0.56          | (r2_hidden @ X0 @ sk_B)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(dt_k2_pre_topc, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.56       ( m1_subset_1 @
% 0.37/0.56         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X7)
% 0.37/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.37/0.56          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C_1) @ 
% 0.37/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.56  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C_1) @ 
% 0.37/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf(l3_subset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X4 @ X5)
% 0.37/0.56          | (r2_hidden @ X4 @ X6)
% 0.37/0.56          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.37/0.56      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r2_hidden @ X0 @ sk_B)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1)))),
% 0.37/0.56      inference('clc', [status(thm)], ['11', '18'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_C_1) @ X0)
% 0.37/0.56          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1)) @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '19'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (((r1_tarski @ (k2_pre_topc @ sk_A @ sk_C_1) @ sk_B)
% 0.37/0.56        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_C_1) @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf('23', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_C_1) @ sk_B)),
% 0.37/0.56      inference('simplify', [status(thm)], ['22'])).
% 0.37/0.56  thf('24', plain, ($false), inference('demod', [status(thm)], ['0', '23'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
