%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4sA9pwxOSY

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:40 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   56 (  65 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  317 ( 456 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t10_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ~ ( ( B != k1_xboole_0 )
            & ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ~ ( r2_hidden @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_subset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X22: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r1_tarski @ X17 @ X15 )
      | ( X16
       != ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_tarski @ X17 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B_2 @ sk_A )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r1_xboole_0 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( m1_subset_1 @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X23: $i] :
      ( ~ ( r2_hidden @ X23 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X23 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_2 )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B_2 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_2 )
    | ( r1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_A @ sk_B_2 ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['12','29'])).

thf('31',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','30'])).

thf('32',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4sA9pwxOSY
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:22:49 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.33/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.33/0.52  % Solved by: fo/fo7.sh
% 0.33/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.52  % done 134 iterations in 0.051s
% 0.33/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.33/0.52  % SZS output start Refutation
% 0.33/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.33/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.33/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.33/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.33/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.33/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.33/0.52  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.33/0.52  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.33/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.33/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.33/0.52  thf(t7_xboole_0, axiom,
% 0.33/0.52    (![A:$i]:
% 0.33/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.33/0.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.33/0.52  thf('0', plain,
% 0.33/0.52      (![X11 : $i]:
% 0.33/0.52         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X11) @ X11))),
% 0.33/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.33/0.52  thf(t10_subset_1, conjecture,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.33/0.52       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.33/0.52            ( ![C:$i]:
% 0.33/0.52              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.33/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.52    (~( ![A:$i,B:$i]:
% 0.33/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.33/0.52          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.33/0.52               ( ![C:$i]:
% 0.33/0.52                 ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ) )),
% 0.33/0.52    inference('cnf.neg', [status(esa)], [t10_subset_1])).
% 0.33/0.52  thf('1', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(d2_subset_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( ( v1_xboole_0 @ A ) =>
% 0.33/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.33/0.52       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.33/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.33/0.52  thf('2', plain,
% 0.33/0.52      (![X19 : $i, X20 : $i]:
% 0.33/0.52         (~ (m1_subset_1 @ X19 @ X20)
% 0.33/0.52          | (r2_hidden @ X19 @ X20)
% 0.33/0.52          | (v1_xboole_0 @ X20))),
% 0.33/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.33/0.52  thf('3', plain,
% 0.33/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.33/0.52        | (r2_hidden @ sk_B_2 @ (k1_zfmisc_1 @ sk_A)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.33/0.52  thf(fc1_subset_1, axiom,
% 0.33/0.52    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.33/0.52  thf('4', plain, (![X22 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 0.33/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.33/0.52  thf('5', plain, ((r2_hidden @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.33/0.52      inference('clc', [status(thm)], ['3', '4'])).
% 0.33/0.52  thf(d1_zfmisc_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.33/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.33/0.52  thf('6', plain,
% 0.33/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X17 @ X16)
% 0.33/0.52          | (r1_tarski @ X17 @ X15)
% 0.33/0.52          | ((X16) != (k1_zfmisc_1 @ X15)))),
% 0.33/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.33/0.52  thf('7', plain,
% 0.33/0.52      (![X15 : $i, X17 : $i]:
% 0.33/0.52         ((r1_tarski @ X17 @ X15) | ~ (r2_hidden @ X17 @ (k1_zfmisc_1 @ X15)))),
% 0.33/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.33/0.52  thf('8', plain, ((r1_tarski @ sk_B_2 @ sk_A)),
% 0.33/0.52      inference('sup-', [status(thm)], ['5', '7'])).
% 0.33/0.52  thf(t28_xboole_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.33/0.52  thf('9', plain,
% 0.33/0.52      (![X12 : $i, X13 : $i]:
% 0.33/0.52         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.33/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.33/0.52  thf('10', plain, (((k3_xboole_0 @ sk_B_2 @ sk_A) = (sk_B_2))),
% 0.33/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.33/0.52  thf(t4_xboole_0, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.33/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.33/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.33/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.33/0.52  thf('11', plain,
% 0.33/0.52      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.33/0.52          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.33/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.33/0.52  thf('12', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X0 @ sk_B_2) | ~ (r1_xboole_0 @ sk_B_2 @ sk_A))),
% 0.33/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.33/0.52  thf(t3_xboole_0, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.33/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.33/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.33/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.33/0.52  thf('13', plain,
% 0.33/0.52      (![X3 : $i, X4 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.33/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.33/0.52  thf('14', plain,
% 0.33/0.52      (![X19 : $i, X20 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X19 @ X20)
% 0.33/0.52          | (m1_subset_1 @ X19 @ X20)
% 0.33/0.52          | (v1_xboole_0 @ X20))),
% 0.33/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.33/0.52  thf(d1_xboole_0, axiom,
% 0.33/0.52    (![A:$i]:
% 0.33/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.33/0.52  thf('15', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.33/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.33/0.52  thf('16', plain,
% 0.33/0.52      (![X19 : $i, X20 : $i]:
% 0.33/0.52         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.33/0.52      inference('clc', [status(thm)], ['14', '15'])).
% 0.33/0.52  thf('17', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ X0 @ X1) | (m1_subset_1 @ (sk_C @ X1 @ X0) @ X0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['13', '16'])).
% 0.33/0.52  thf('18', plain,
% 0.33/0.52      (![X3 : $i, X4 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.33/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.33/0.52  thf('19', plain,
% 0.33/0.52      (![X23 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X23 @ sk_B_2) | ~ (m1_subset_1 @ X23 @ sk_A))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('20', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ X0 @ sk_B_2)
% 0.33/0.52          | ~ (m1_subset_1 @ (sk_C @ sk_B_2 @ X0) @ sk_A))),
% 0.33/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.33/0.52  thf('21', plain,
% 0.33/0.52      (((r1_xboole_0 @ sk_A @ sk_B_2) | (r1_xboole_0 @ sk_A @ sk_B_2))),
% 0.33/0.52      inference('sup-', [status(thm)], ['17', '20'])).
% 0.33/0.52  thf('22', plain, ((r1_xboole_0 @ sk_A @ sk_B_2)),
% 0.33/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.33/0.52  thf('23', plain,
% 0.33/0.52      (![X3 : $i, X4 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.33/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.33/0.52  thf('24', plain,
% 0.33/0.52      (![X3 : $i, X4 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.33/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.33/0.52  thf('25', plain,
% 0.33/0.52      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X5 @ X3)
% 0.33/0.52          | ~ (r2_hidden @ X5 @ X6)
% 0.33/0.52          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.33/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.33/0.52  thf('26', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ X1 @ X0)
% 0.33/0.52          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.33/0.52          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.33/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.33/0.52  thf('27', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r1_xboole_0 @ X0 @ X1)
% 0.33/0.52          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.33/0.52          | (r1_xboole_0 @ X0 @ X1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['23', '26'])).
% 0.33/0.52  thf('28', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.33/0.52      inference('simplify', [status(thm)], ['27'])).
% 0.33/0.52  thf('29', plain, ((r1_xboole_0 @ sk_B_2 @ sk_A)),
% 0.33/0.52      inference('sup-', [status(thm)], ['22', '28'])).
% 0.33/0.52  thf('30', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_2)),
% 0.33/0.52      inference('demod', [status(thm)], ['12', '29'])).
% 0.33/0.52  thf('31', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['0', '30'])).
% 0.33/0.52  thf('32', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('33', plain, ($false),
% 0.33/0.52      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.33/0.52  
% 0.33/0.52  % SZS output end Refutation
% 0.33/0.52  
% 0.33/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
