%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yj6YRI8iLi

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:58 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   62 (  74 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  401 ( 562 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t42_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k9_subset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k9_subset_1 @ X23 @ X21 @ X22 )
        = ( k3_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k4_xboole_0 @ X5 @ X4 ) @ ( k4_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X20: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('19',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r1_tarski @ X13 @ X11 )
      | ( X12
       != ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ( X12
       != ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X20: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','33'])).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['4','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yj6YRI8iLi
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:40:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.77  % Solved by: fo/fo7.sh
% 0.52/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.77  % done 554 iterations in 0.306s
% 0.52/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.77  % SZS output start Refutation
% 0.52/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.77  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.52/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.77  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.52/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.77  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.52/0.77  thf(t42_subset_1, conjecture,
% 0.52/0.77    (![A:$i,B:$i]:
% 0.52/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.77       ( ![C:$i]:
% 0.52/0.77         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.77           ( r1_tarski @
% 0.52/0.77             ( k3_subset_1 @ A @ B ) @ 
% 0.52/0.77             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.52/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.77    (~( ![A:$i,B:$i]:
% 0.52/0.77        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.77          ( ![C:$i]:
% 0.52/0.77            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.77              ( r1_tarski @
% 0.52/0.77                ( k3_subset_1 @ A @ B ) @ 
% 0.52/0.77                ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ) )),
% 0.52/0.77    inference('cnf.neg', [status(esa)], [t42_subset_1])).
% 0.52/0.77  thf('0', plain,
% 0.52/0.77      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.52/0.77          (k3_subset_1 @ sk_A @ (k9_subset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf(redefinition_k9_subset_1, axiom,
% 0.52/0.77    (![A:$i,B:$i,C:$i]:
% 0.52/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.77       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.52/0.77  thf('2', plain,
% 0.52/0.77      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.52/0.77         (((k9_subset_1 @ X23 @ X21 @ X22) = (k3_xboole_0 @ X21 @ X22))
% 0.52/0.77          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.52/0.77      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.52/0.77  thf('3', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         ((k9_subset_1 @ sk_A @ X0 @ sk_C_1) = (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.52/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.77  thf('4', plain,
% 0.52/0.77      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.52/0.77          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 0.52/0.77      inference('demod', [status(thm)], ['0', '3'])).
% 0.52/0.77  thf('5', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf(d5_subset_1, axiom,
% 0.52/0.77    (![A:$i,B:$i]:
% 0.52/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.77       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.52/0.77  thf('6', plain,
% 0.52/0.77      (![X18 : $i, X19 : $i]:
% 0.52/0.77         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.52/0.77          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.52/0.77      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.52/0.77  thf('7', plain,
% 0.52/0.77      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.77  thf(t48_xboole_1, axiom,
% 0.52/0.77    (![A:$i,B:$i]:
% 0.52/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.77  thf('8', plain,
% 0.52/0.77      (![X8 : $i, X9 : $i]:
% 0.52/0.77         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.52/0.77           = (k3_xboole_0 @ X8 @ X9))),
% 0.52/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.77  thf(t36_xboole_1, axiom,
% 0.52/0.77    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.52/0.77  thf('9', plain,
% 0.52/0.77      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.52/0.77      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.52/0.77  thf('10', plain,
% 0.52/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.52/0.77      inference('sup+', [status(thm)], ['8', '9'])).
% 0.52/0.77  thf(t34_xboole_1, axiom,
% 0.52/0.77    (![A:$i,B:$i,C:$i]:
% 0.52/0.77     ( ( r1_tarski @ A @ B ) =>
% 0.52/0.77       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.52/0.77  thf('11', plain,
% 0.52/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.52/0.77         (~ (r1_tarski @ X3 @ X4)
% 0.52/0.77          | (r1_tarski @ (k4_xboole_0 @ X5 @ X4) @ (k4_xboole_0 @ X5 @ X3)))),
% 0.52/0.77      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.52/0.77  thf('12', plain,
% 0.52/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.77         (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ 
% 0.52/0.77          (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.77  thf('13', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.52/0.77          (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.52/0.77      inference('sup+', [status(thm)], ['7', '12'])).
% 0.52/0.77  thf('14', plain,
% 0.52/0.77      (![X8 : $i, X9 : $i]:
% 0.52/0.77         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.52/0.77           = (k3_xboole_0 @ X8 @ X9))),
% 0.52/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.77  thf('15', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.77  thf(d2_subset_1, axiom,
% 0.52/0.77    (![A:$i,B:$i]:
% 0.52/0.77     ( ( ( v1_xboole_0 @ A ) =>
% 0.52/0.77         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.52/0.77       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.52/0.77         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.52/0.77  thf('16', plain,
% 0.52/0.77      (![X15 : $i, X16 : $i]:
% 0.52/0.77         (~ (m1_subset_1 @ X15 @ X16)
% 0.52/0.77          | (r2_hidden @ X15 @ X16)
% 0.52/0.77          | (v1_xboole_0 @ X16))),
% 0.52/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.52/0.77  thf('17', plain,
% 0.52/0.77      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.77        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.77  thf(fc1_subset_1, axiom,
% 0.52/0.77    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.52/0.77  thf('18', plain, (![X20 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.52/0.77      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.52/0.77  thf('19', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.77      inference('clc', [status(thm)], ['17', '18'])).
% 0.52/0.77  thf(d1_zfmisc_1, axiom,
% 0.52/0.77    (![A:$i,B:$i]:
% 0.52/0.77     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.52/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.52/0.77  thf('20', plain,
% 0.52/0.77      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.52/0.77         (~ (r2_hidden @ X13 @ X12)
% 0.52/0.77          | (r1_tarski @ X13 @ X11)
% 0.52/0.77          | ((X12) != (k1_zfmisc_1 @ X11)))),
% 0.52/0.77      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.52/0.77  thf('21', plain,
% 0.52/0.77      (![X11 : $i, X13 : $i]:
% 0.52/0.77         ((r1_tarski @ X13 @ X11) | ~ (r2_hidden @ X13 @ (k1_zfmisc_1 @ X11)))),
% 0.52/0.77      inference('simplify', [status(thm)], ['20'])).
% 0.52/0.77  thf('22', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.52/0.77      inference('sup-', [status(thm)], ['19', '21'])).
% 0.52/0.77  thf('23', plain,
% 0.52/0.77      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.52/0.77      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.52/0.77  thf(t1_xboole_1, axiom,
% 0.52/0.77    (![A:$i,B:$i,C:$i]:
% 0.52/0.77     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.52/0.77       ( r1_tarski @ A @ C ) ))).
% 0.52/0.77  thf('24', plain,
% 0.52/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.77         (~ (r1_tarski @ X0 @ X1)
% 0.52/0.77          | ~ (r1_tarski @ X1 @ X2)
% 0.52/0.77          | (r1_tarski @ X0 @ X2))),
% 0.52/0.77      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.52/0.77  thf('25', plain,
% 0.52/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.77         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.52/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.77  thf('26', plain,
% 0.52/0.77      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.52/0.77      inference('sup-', [status(thm)], ['22', '25'])).
% 0.52/0.77  thf('27', plain,
% 0.52/0.77      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.77         (~ (r1_tarski @ X10 @ X11)
% 0.52/0.77          | (r2_hidden @ X10 @ X12)
% 0.52/0.77          | ((X12) != (k1_zfmisc_1 @ X11)))),
% 0.52/0.77      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.52/0.77  thf('28', plain,
% 0.52/0.77      (![X10 : $i, X11 : $i]:
% 0.52/0.77         ((r2_hidden @ X10 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X10 @ X11))),
% 0.52/0.77      inference('simplify', [status(thm)], ['27'])).
% 0.52/0.77  thf('29', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (r2_hidden @ (k4_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.77      inference('sup-', [status(thm)], ['26', '28'])).
% 0.52/0.77  thf('30', plain,
% 0.52/0.77      (![X15 : $i, X16 : $i]:
% 0.52/0.77         (~ (r2_hidden @ X15 @ X16)
% 0.52/0.77          | (m1_subset_1 @ X15 @ X16)
% 0.52/0.77          | (v1_xboole_0 @ X16))),
% 0.52/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.52/0.77  thf('31', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.77          | (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.52/0.77  thf('32', plain, (![X20 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.52/0.77      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.52/0.77  thf('33', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.77      inference('clc', [status(thm)], ['31', '32'])).
% 0.52/0.77  thf('34', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.77      inference('sup+', [status(thm)], ['14', '33'])).
% 0.52/0.77  thf('35', plain,
% 0.52/0.77      (![X18 : $i, X19 : $i]:
% 0.52/0.77         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.52/0.77          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.52/0.77      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.52/0.77  thf('36', plain,
% 0.52/0.77      (![X0 : $i]:
% 0.52/0.77         ((k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.52/0.77           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.52/0.77      inference('sup-', [status(thm)], ['34', '35'])).
% 0.59/0.77  thf('37', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.59/0.77          (k3_subset_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.59/0.77      inference('demod', [status(thm)], ['13', '36'])).
% 0.59/0.77  thf('38', plain, ($false), inference('demod', [status(thm)], ['4', '37'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
