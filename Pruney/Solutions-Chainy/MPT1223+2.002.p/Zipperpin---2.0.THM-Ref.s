%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lpaMUpMLH3

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:45 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   45 (  61 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  357 ( 697 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lpaMUpMLH3
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:56:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 233 iterations in 0.209s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.64  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(t31_tops_1, conjecture,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.45/0.64                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i]:
% 0.45/0.64        ( ( l1_pre_topc @ A ) =>
% 0.45/0.64          ( ![B:$i]:
% 0.45/0.64            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64              ( ![C:$i]:
% 0.45/0.64                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64                  ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.45/0.64                    ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t31_tops_1])).
% 0.45/0.64  thf('0', plain, (~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_C_1) @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(d3_tarski, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (![X1 : $i, X3 : $i]:
% 0.45/0.64         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t45_pre_topc, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_pre_topc @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.64               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.45/0.64                 ( ![D:$i]:
% 0.45/0.64                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.64                     ( ( ( v4_pre_topc @ D @ A ) & ( r1_tarski @ B @ D ) ) =>
% 0.45/0.64                       ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.45/0.64          | ~ (r2_hidden @ X11 @ (k2_pre_topc @ X10 @ X9))
% 0.45/0.64          | ~ (v4_pre_topc @ X12 @ X10)
% 0.45/0.64          | ~ (r1_tarski @ X9 @ X12)
% 0.45/0.64          | (r2_hidden @ X11 @ X12)
% 0.45/0.64          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.45/0.64          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X10))
% 0.45/0.64          | ~ (l1_pre_topc @ X10))),
% 0.45/0.64      inference('cnf', [status(esa)], [t45_pre_topc])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ sk_A)
% 0.45/0.64          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64          | (r2_hidden @ X0 @ X1)
% 0.45/0.64          | ~ (r1_tarski @ sk_C_1 @ X1)
% 0.45/0.64          | ~ (v4_pre_topc @ X1 @ sk_A)
% 0.45/0.64          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.64  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64          | (r2_hidden @ X0 @ X1)
% 0.45/0.64          | ~ (r1_tarski @ sk_C_1 @ X1)
% 0.45/0.64          | ~ (v4_pre_topc @ X1 @ sk_A)
% 0.45/0.64          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1)))),
% 0.45/0.64      inference('demod', [status(thm)], ['5', '6'])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 0.45/0.64          | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.45/0.64          | ~ (r1_tarski @ sk_C_1 @ sk_B)
% 0.45/0.64          | (r2_hidden @ X0 @ sk_B)
% 0.45/0.64          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '7'])).
% 0.45/0.64  thf('9', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('10', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 0.45/0.64          | (r2_hidden @ X0 @ sk_B)
% 0.45/0.64          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(dt_k2_pre_topc, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( l1_pre_topc @ A ) & 
% 0.45/0.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.64       ( m1_subset_1 @
% 0.45/0.64         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i]:
% 0.45/0.64         (~ (l1_pre_topc @ X7)
% 0.45/0.64          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.45/0.64          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C_1) @ 
% 0.45/0.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.64        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.64  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C_1) @ 
% 0.45/0.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf(t3_subset, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X4 : $i, X5 : $i]:
% 0.45/0.64         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.64          | (r2_hidden @ X0 @ X2)
% 0.45/0.64          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.64          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((r2_hidden @ X0 @ sk_B)
% 0.45/0.64          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1)))),
% 0.45/0.64      inference('clc', [status(thm)], ['11', '20'])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_C_1) @ X0)
% 0.45/0.64          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1)) @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '21'])).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      (![X1 : $i, X3 : $i]:
% 0.45/0.64         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      (((r1_tarski @ (k2_pre_topc @ sk_A @ sk_C_1) @ sk_B)
% 0.45/0.64        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_C_1) @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.64  thf('25', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_C_1) @ sk_B)),
% 0.45/0.64      inference('simplify', [status(thm)], ['24'])).
% 0.45/0.64  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
