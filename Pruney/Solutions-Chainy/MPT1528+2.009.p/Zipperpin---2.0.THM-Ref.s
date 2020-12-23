%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gk3tlpsmtR

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   50 (  69 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  269 ( 485 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_lattice3_type,type,(
    r1_lattice3: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( sk_B @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(t6_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
            & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( r2_lattice3 @ A @ k1_xboole_0 @ B )
              & ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_yellow_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r2_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X14 @ X13 ) @ X14 )
      | ( r2_lattice3 @ X13 @ X14 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_lattice3])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_B_1 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_B_1 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 )
    | ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 )
   <= ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( sk_B @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
         => ( ( r1_lattice3 @ A @ B @ C )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ D @ B )
                 => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X10 @ X9 ) @ X10 )
      | ( r1_lattice3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_lattice3])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( r1_lattice3 @ sk_A @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,
    ( ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 )
   <= ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('22',plain,(
    r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 )
    | ~ ( r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('24',plain,(
    ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['11','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['9','25'])).

thf('27',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gk3tlpsmtR
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 48 iterations in 0.038s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.54  thf(r1_lattice3_type, type, r1_lattice3: $i > $i > $i > $o).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.54  thf(r2_lattice3_type, type, r2_lattice3: $i > $i > $i > $o).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.54  thf(rc2_subset_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ?[B:$i]:
% 0.37/0.54       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.37/0.54  thf('0', plain, (![X0 : $i]: (v1_xboole_0 @ (sk_B @ X0))),
% 0.37/0.54      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.37/0.54  thf(t6_yellow_0, conjecture,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( l1_orders_2 @ A ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.54           ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.37/0.54             ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i]:
% 0.37/0.54        ( ( l1_orders_2 @ A ) =>
% 0.37/0.54          ( ![B:$i]:
% 0.37/0.54            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.54              ( ( r2_lattice3 @ A @ k1_xboole_0 @ B ) & 
% 0.37/0.54                ( r1_lattice3 @ A @ k1_xboole_0 @ B ) ) ) ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t6_yellow_0])).
% 0.37/0.54  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(d9_lattice3, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( l1_orders_2 @ A ) =>
% 0.37/0.54       ( ![B:$i,C:$i]:
% 0.37/0.54         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.54           ( ( r2_lattice3 @ A @ B @ C ) <=>
% 0.37/0.54             ( ![D:$i]:
% 0.37/0.54               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.54                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ D @ C ) ) ) ) ) ) ) ))).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.37/0.54          | (r2_hidden @ (sk_D_1 @ X12 @ X14 @ X13) @ X14)
% 0.37/0.54          | (r2_lattice3 @ X13 @ X14 @ X12)
% 0.37/0.54          | ~ (l1_orders_2 @ X13))),
% 0.37/0.54      inference('cnf', [status(esa)], [d9_lattice3])).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (l1_orders_2 @ sk_A)
% 0.37/0.54          | (r2_lattice3 @ sk_A @ X0 @ sk_B_1)
% 0.37/0.54          | (r2_hidden @ (sk_D_1 @ sk_B_1 @ X0 @ sk_A) @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.54  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r2_lattice3 @ sk_A @ X0 @ sk_B_1)
% 0.37/0.54          | (r2_hidden @ (sk_D_1 @ sk_B_1 @ X0 @ sk_A) @ X0))),
% 0.37/0.54      inference('demod', [status(thm)], ['3', '4'])).
% 0.37/0.54  thf(t4_subset_1, axiom,
% 0.37/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.54  thf(t5_subset, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.37/0.54          ( v1_xboole_0 @ C ) ) ))).
% 0.37/0.54  thf('7', plain,
% 0.37/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X5 @ X6)
% 0.37/0.54          | ~ (v1_xboole_0 @ X7)
% 0.37/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['5', '8'])).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      ((~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1)
% 0.37/0.54        | ~ (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      ((~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1))
% 0.37/0.54         <= (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.37/0.54      inference('split', [status(esa)], ['10'])).
% 0.37/0.54  thf('12', plain, (![X0 : $i]: (v1_xboole_0 @ (sk_B @ X0))),
% 0.37/0.54      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.37/0.54  thf('13', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(d8_lattice3, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( l1_orders_2 @ A ) =>
% 0.37/0.54       ( ![B:$i,C:$i]:
% 0.37/0.54         ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.54           ( ( r1_lattice3 @ A @ B @ C ) <=>
% 0.37/0.54             ( ![D:$i]:
% 0.37/0.54               ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.54                 ( ( r2_hidden @ D @ B ) => ( r1_orders_2 @ A @ C @ D ) ) ) ) ) ) ) ))).
% 0.37/0.54  thf('14', plain,
% 0.37/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.37/0.54          | (r2_hidden @ (sk_D @ X8 @ X10 @ X9) @ X10)
% 0.37/0.54          | (r1_lattice3 @ X9 @ X10 @ X8)
% 0.37/0.54          | ~ (l1_orders_2 @ X9))),
% 0.37/0.54      inference('cnf', [status(esa)], [d8_lattice3])).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (l1_orders_2 @ sk_A)
% 0.37/0.54          | (r1_lattice3 @ sk_A @ X0 @ sk_B_1)
% 0.37/0.54          | (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ sk_A) @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.54  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('17', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r1_lattice3 @ sk_A @ X0 @ sk_B_1)
% 0.37/0.54          | (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ sk_A) @ X0))),
% 0.37/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.54  thf('19', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.54  thf('20', plain, ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1)),
% 0.37/0.54      inference('sup-', [status(thm)], ['12', '19'])).
% 0.37/0.54  thf('21', plain,
% 0.37/0.54      ((~ (r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1))
% 0.37/0.54         <= (~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1)))),
% 0.37/0.54      inference('split', [status(esa)], ['10'])).
% 0.37/0.54  thf('22', plain, (((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1)) | 
% 0.37/0.54       ~ ((r1_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1))),
% 0.37/0.54      inference('split', [status(esa)], ['10'])).
% 0.37/0.54  thf('24', plain, (~ ((r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1))),
% 0.37/0.54      inference('sat_resolution*', [status(thm)], ['22', '23'])).
% 0.37/0.54  thf('25', plain, (~ (r2_lattice3 @ sk_A @ k1_xboole_0 @ sk_B_1)),
% 0.37/0.54      inference('simpl_trail', [status(thm)], ['11', '24'])).
% 0.37/0.54  thf('26', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.37/0.54      inference('clc', [status(thm)], ['9', '25'])).
% 0.37/0.54  thf('27', plain, ($false), inference('sup-', [status(thm)], ['0', '26'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
