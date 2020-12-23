%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rYaKLTgbvO

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:07 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   42 (  54 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  290 ( 566 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t46_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( ( r1_xboole_0 @ B @ C )
              & ( r1_xboole_0 @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) )
           => ( B
              = ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( ( r1_xboole_0 @ B @ C )
                & ( r1_xboole_0 @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) )
             => ( B
                = ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_subset_1])).

thf('0',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_xboole_0 @ X14 @ ( k3_subset_1 @ X13 @ X12 ) )
      | ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('9',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['6','9'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r2_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('12',plain,(
    ~ ( r2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_xboole_0 @ X11 @ X9 )
      | ( r1_tarski @ X11 @ ( k3_subset_1 @ X10 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_C )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('21',plain,
    ( ( sk_B
      = ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_B
 != ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['12','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rYaKLTgbvO
% 0.16/0.37  % Computer   : n021.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 14:04:34 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.53  % Solved by: fo/fo7.sh
% 0.23/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.53  % done 70 iterations in 0.046s
% 0.23/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.53  % SZS output start Refutation
% 0.23/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.53  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.23/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.53  thf(t46_subset_1, conjecture,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.53       ( ![C:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.53           ( ( ( r1_xboole_0 @ B @ C ) & 
% 0.23/0.53               ( r1_xboole_0 @
% 0.23/0.53                 ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.23/0.53             ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.23/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.53    (~( ![A:$i,B:$i]:
% 0.23/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.53          ( ![C:$i]:
% 0.23/0.53            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.53              ( ( ( r1_xboole_0 @ B @ C ) & 
% 0.23/0.53                  ( r1_xboole_0 @
% 0.23/0.53                    ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.23/0.53                ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.23/0.53    inference('cnf.neg', [status(esa)], [t46_subset_1])).
% 0.23/0.53  thf('0', plain,
% 0.23/0.53      ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(symmetry_r1_xboole_0, axiom,
% 0.23/0.53    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.23/0.53  thf('1', plain,
% 0.23/0.53      (![X3 : $i, X4 : $i]:
% 0.23/0.53         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.23/0.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.23/0.53  thf('2', plain,
% 0.23/0.53      ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.23/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.53  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(t44_subset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.53       ( ![C:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.53           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.23/0.53             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.23/0.53  thf('4', plain,
% 0.23/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.23/0.53          | ~ (r1_xboole_0 @ X14 @ (k3_subset_1 @ X13 @ X12))
% 0.23/0.53          | (r1_tarski @ X14 @ X12)
% 0.23/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.23/0.53      inference('cnf', [status(esa)], [t44_subset_1])).
% 0.23/0.53  thf('5', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.53          | (r1_tarski @ X0 @ sk_B)
% 0.23/0.53          | ~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.53  thf('6', plain,
% 0.23/0.53      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B)
% 0.23/0.53        | ~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['2', '5'])).
% 0.23/0.53  thf('7', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(dt_k3_subset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.53       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.53  thf('8', plain,
% 0.23/0.53      (![X7 : $i, X8 : $i]:
% 0.23/0.53         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 0.23/0.53          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.23/0.53      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.23/0.53  thf('9', plain,
% 0.23/0.53      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.53  thf('10', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B)),
% 0.23/0.53      inference('demod', [status(thm)], ['6', '9'])).
% 0.23/0.53  thf(t60_xboole_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.23/0.53  thf('11', plain,
% 0.23/0.53      (![X5 : $i, X6 : $i]:
% 0.23/0.53         (~ (r1_tarski @ X5 @ X6) | ~ (r2_xboole_0 @ X6 @ X5))),
% 0.23/0.53      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.23/0.53  thf('12', plain, (~ (r2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.23/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.53  thf('13', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(t43_subset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.53       ( ![C:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.53           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.23/0.53             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.23/0.53  thf('15', plain,
% 0.23/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.23/0.53          | ~ (r1_xboole_0 @ X11 @ X9)
% 0.23/0.53          | (r1_tarski @ X11 @ (k3_subset_1 @ X10 @ X9))
% 0.23/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.23/0.53      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.23/0.53  thf('16', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.53          | (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.23/0.53          | ~ (r1_xboole_0 @ X0 @ sk_C))),
% 0.23/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.53  thf('17', plain,
% 0.23/0.53      ((~ (r1_xboole_0 @ sk_B @ sk_C)
% 0.23/0.53        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['13', '16'])).
% 0.23/0.53  thf('18', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('19', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.23/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.23/0.53  thf(d8_xboole_0, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.23/0.53       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.23/0.53  thf('20', plain,
% 0.23/0.53      (![X0 : $i, X2 : $i]:
% 0.23/0.53         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.23/0.53      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.23/0.53  thf('21', plain,
% 0.23/0.53      ((((sk_B) = (k3_subset_1 @ sk_A @ sk_C))
% 0.23/0.53        | (r2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.53  thf('22', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('23', plain, ((r2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.23/0.53      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.23/0.53  thf('24', plain, ($false), inference('demod', [status(thm)], ['12', '23'])).
% 0.23/0.53  
% 0.23/0.53  % SZS output end Refutation
% 0.23/0.53  
% 0.23/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
