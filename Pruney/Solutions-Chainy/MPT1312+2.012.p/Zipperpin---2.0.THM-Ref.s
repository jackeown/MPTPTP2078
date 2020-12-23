%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sz64Q4x9Iz

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  55 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :   15
%              Number of atoms          :  286 ( 413 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t31_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
               => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_tops_2])).

thf('0',plain,(
    ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X4: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sz64Q4x9Iz
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 82 iterations in 0.041s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(t31_tops_2, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @
% 0.20/0.53                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.20/0.53               ( m1_subset_1 @
% 0.20/0.53                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( l1_pre_topc @ A ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53              ( ![C:$i]:
% 0.20/0.53                ( ( m1_subset_1 @
% 0.20/0.53                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.20/0.53                  ( m1_subset_1 @
% 0.20/0.53                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t31_tops_2])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (~ (m1_subset_1 @ sk_C_1 @ 
% 0.20/0.53          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d3_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((r1_tarski @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | (r2_hidden @ X0 @ X2)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ sk_C_1 @ X0)
% 0.20/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.53  thf(t1_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ sk_C_1 @ X0)
% 0.20/0.53          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf(t39_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.53               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.53          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.53          | ~ (l1_pre_topc @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r1_tarski @ sk_C_1 @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X1)
% 0.20/0.53          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.53          | ~ (m1_pre_topc @ sk_B @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | (r1_tarski @ sk_C_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '12'])).
% 0.20/0.53  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | (r1_tarski @ sk_C_1 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf(t2_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         ((r2_hidden @ X7 @ X8)
% 0.20/0.53          | (v1_xboole_0 @ X8)
% 0.20/0.53          | ~ (m1_subset_1 @ X7 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ sk_C_1 @ X0)
% 0.20/0.53          | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf(fc1_subset_1, axiom,
% 0.20/0.53    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.53  thf('18', plain, (![X4 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | (r1_tarski @ sk_C_1 @ X0))),
% 0.20/0.53      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (((r1_tarski @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53        | (r1_tarski @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((r1_tarski @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X9 : $i, X11 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
