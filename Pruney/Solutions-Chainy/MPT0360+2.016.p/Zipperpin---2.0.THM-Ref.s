%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YfksYFKprW

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:43 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   47 (  53 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  248 ( 338 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('1',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('12',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B_1 ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','18'])).

thf('20',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YfksYFKprW
% 0.15/0.37  % Computer   : n021.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 17:20:04 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.47  % Solved by: fo/fo7.sh
% 0.24/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.47  % done 101 iterations in 0.024s
% 0.24/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.47  % SZS output start Refutation
% 0.24/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.24/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.24/0.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.24/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.24/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.47  thf(t7_xboole_0, axiom,
% 0.24/0.47    (![A:$i]:
% 0.24/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.24/0.47  thf('0', plain,
% 0.24/0.47      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.24/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.24/0.47  thf(t40_subset_1, conjecture,
% 0.24/0.47    (![A:$i,B:$i,C:$i]:
% 0.24/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.47       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.24/0.47         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.24/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.47        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.47          ( ( ( r1_tarski @ B @ C ) & 
% 0.24/0.47              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.24/0.47            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.24/0.47    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.24/0.47  thf('1', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf(t28_xboole_1, axiom,
% 0.24/0.47    (![A:$i,B:$i]:
% 0.24/0.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.24/0.47  thf('2', plain,
% 0.24/0.47      (![X11 : $i, X12 : $i]:
% 0.24/0.47         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.24/0.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.24/0.47  thf('3', plain,
% 0.24/0.47      (((k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_1)) = (sk_B_1))),
% 0.24/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.47  thf(commutativity_k3_xboole_0, axiom,
% 0.24/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.24/0.47  thf('4', plain,
% 0.24/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.24/0.47  thf(t4_xboole_0, axiom,
% 0.24/0.47    (![A:$i,B:$i]:
% 0.24/0.47     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.24/0.47  thf('5', plain,
% 0.24/0.47      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.24/0.47         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.24/0.47          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.24/0.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.24/0.47  thf('6', plain,
% 0.24/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.24/0.47          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.24/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.47  thf('7', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.24/0.47          | ~ (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B_1))),
% 0.24/0.47      inference('sup-', [status(thm)], ['3', '6'])).
% 0.24/0.47  thf('8', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf(d5_subset_1, axiom,
% 0.24/0.47    (![A:$i,B:$i]:
% 0.24/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.47       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.24/0.47  thf('9', plain,
% 0.24/0.47      (![X19 : $i, X20 : $i]:
% 0.24/0.47         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.24/0.47          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.24/0.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.24/0.47  thf('10', plain,
% 0.24/0.47      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.24/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.47  thf(t79_xboole_1, axiom,
% 0.24/0.47    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.24/0.47  thf('11', plain,
% 0.24/0.47      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.24/0.47      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.24/0.47  thf('12', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf(t12_xboole_1, axiom,
% 0.24/0.47    (![A:$i,B:$i]:
% 0.24/0.47     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.24/0.47  thf('13', plain,
% 0.24/0.47      (![X9 : $i, X10 : $i]:
% 0.24/0.47         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.24/0.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.24/0.47  thf('14', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.24/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.47  thf(t70_xboole_1, axiom,
% 0.24/0.47    (![A:$i,B:$i,C:$i]:
% 0.24/0.47     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.24/0.47            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.24/0.47       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.24/0.47            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.24/0.47  thf('15', plain,
% 0.24/0.47      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.24/0.47         ((r1_xboole_0 @ X13 @ X14)
% 0.24/0.47          | ~ (r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X16)))),
% 0.24/0.47      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.24/0.47  thf('16', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         (~ (r1_xboole_0 @ X0 @ sk_C_1) | (r1_xboole_0 @ X0 @ sk_B_1))),
% 0.24/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.24/0.47  thf('17', plain,
% 0.24/0.47      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_B_1)),
% 0.24/0.47      inference('sup-', [status(thm)], ['11', '16'])).
% 0.24/0.47  thf('18', plain, ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B_1)),
% 0.24/0.47      inference('sup+', [status(thm)], ['10', '17'])).
% 0.24/0.47  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.24/0.47      inference('demod', [status(thm)], ['7', '18'])).
% 0.24/0.47  thf('20', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.24/0.47      inference('sup-', [status(thm)], ['0', '19'])).
% 0.24/0.47  thf('21', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('22', plain, ($false),
% 0.24/0.47      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.24/0.47  
% 0.24/0.47  % SZS output end Refutation
% 0.24/0.47  
% 0.24/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
