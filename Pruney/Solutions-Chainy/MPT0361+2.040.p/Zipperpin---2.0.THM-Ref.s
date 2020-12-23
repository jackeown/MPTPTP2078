%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QV3LsvjqDd

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:55 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   36 (  55 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  276 ( 580 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) )
      | ( ( k4_subset_1 @ X6 @ X5 @ X7 )
        = ( k2_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X3 @ X2 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('14',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ( r1_tarski @ ( k3_subset_1 @ X9 @ X8 ) @ ( k3_subset_1 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['6','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QV3LsvjqDd
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.71  % Solved by: fo/fo7.sh
% 0.45/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.71  % done 145 iterations in 0.230s
% 0.45/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.71  % SZS output start Refutation
% 0.45/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.71  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.45/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.71  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.45/0.71  thf(t41_subset_1, conjecture,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.71       ( ![C:$i]:
% 0.45/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.71           ( r1_tarski @
% 0.45/0.71             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.45/0.71             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 0.45/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.71    (~( ![A:$i,B:$i]:
% 0.45/0.71        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.71          ( ![C:$i]:
% 0.45/0.71            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.71              ( r1_tarski @
% 0.45/0.71                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.45/0.71                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 0.45/0.71    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 0.45/0.71  thf('0', plain,
% 0.45/0.71      (~ (r1_tarski @ 
% 0.45/0.71          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.45/0.71          (k3_subset_1 @ sk_A @ sk_B))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(redefinition_k4_subset_1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i]:
% 0.45/0.71     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.45/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.71       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.45/0.71  thf('3', plain,
% 0.45/0.71      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.45/0.71          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6))
% 0.45/0.71          | ((k4_subset_1 @ X6 @ X5 @ X7) = (k2_xboole_0 @ X5 @ X7)))),
% 0.45/0.71      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.45/0.71  thf('4', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.45/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.71  thf('5', plain,
% 0.45/0.71      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.45/0.71      inference('sup-', [status(thm)], ['1', '4'])).
% 0.45/0.71  thf('6', plain,
% 0.45/0.71      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.45/0.71          (k3_subset_1 @ sk_A @ sk_B))),
% 0.45/0.71      inference('demod', [status(thm)], ['0', '5'])).
% 0.45/0.71  thf(t7_xboole_1, axiom,
% 0.45/0.71    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.71  thf('7', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.71      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.45/0.71  thf('8', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(dt_k4_subset_1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i]:
% 0.45/0.71     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.45/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.45/0.71       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.71  thf('10', plain,
% 0.45/0.71      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.45/0.71          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3))
% 0.45/0.71          | (m1_subset_1 @ (k4_subset_1 @ X3 @ X2 @ X4) @ (k1_zfmisc_1 @ X3)))),
% 0.45/0.71      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.45/0.71  thf('11', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ X0) @ 
% 0.45/0.71           (k1_zfmisc_1 @ sk_A))
% 0.45/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.71  thf('12', plain,
% 0.45/0.71      ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['8', '11'])).
% 0.45/0.71  thf('13', plain,
% 0.45/0.71      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.45/0.71      inference('sup-', [status(thm)], ['1', '4'])).
% 0.45/0.71  thf('14', plain,
% 0.45/0.71      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.71  thf(t31_subset_1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.71       ( ![C:$i]:
% 0.45/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.71           ( ( r1_tarski @ B @ C ) <=>
% 0.45/0.71             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.71  thf('15', plain,
% 0.45/0.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.45/0.71          | ~ (r1_tarski @ X10 @ X8)
% 0.45/0.71          | (r1_tarski @ (k3_subset_1 @ X9 @ X8) @ (k3_subset_1 @ X9 @ X10))
% 0.45/0.71          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.45/0.71      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.45/0.71  thf('16', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.45/0.71          | (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.45/0.71             (k3_subset_1 @ sk_A @ X0))
% 0.45/0.71          | ~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.71  thf('17', plain,
% 0.45/0.71      (((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.45/0.71         (k3_subset_1 @ sk_A @ sk_B))
% 0.45/0.71        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['7', '16'])).
% 0.45/0.71  thf('18', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('19', plain,
% 0.45/0.71      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.45/0.71        (k3_subset_1 @ sk_A @ sk_B))),
% 0.45/0.71      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.71  thf('20', plain, ($false), inference('demod', [status(thm)], ['6', '19'])).
% 0.45/0.71  
% 0.45/0.71  % SZS output end Refutation
% 0.45/0.71  
% 0.45/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
