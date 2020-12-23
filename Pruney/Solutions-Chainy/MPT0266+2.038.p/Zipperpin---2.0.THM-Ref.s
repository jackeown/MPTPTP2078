%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ELPfiJH1xf

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  157 ( 189 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t63_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('10',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference(simplify,[status(thm)],['10'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_tarski @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('13',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['0','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ELPfiJH1xf
% 0.17/0.37  % Computer   : n010.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 20:30:29 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.22/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.44  % Solved by: fo/fo7.sh
% 0.22/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.44  % done 20 iterations in 0.008s
% 0.22/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.44  % SZS output start Refutation
% 0.22/0.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.44  thf(t63_zfmisc_1, conjecture,
% 0.22/0.44    (![A:$i,B:$i,C:$i]:
% 0.22/0.44     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.22/0.44       ( r2_hidden @ A @ C ) ))).
% 0.22/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.44        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.22/0.44          ( r2_hidden @ A @ C ) ) )),
% 0.22/0.44    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 0.22/0.44  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf('1', plain,
% 0.22/0.44      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.22/0.44         = (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf(t47_xboole_1, axiom,
% 0.22/0.44    (![A:$i,B:$i]:
% 0.22/0.44     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.44  thf('2', plain,
% 0.22/0.44      (![X6 : $i, X7 : $i]:
% 0.22/0.44         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7))
% 0.22/0.44           = (k4_xboole_0 @ X6 @ X7))),
% 0.22/0.44      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.22/0.44  thf('3', plain,
% 0.22/0.44      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_A @ sk_B))
% 0.22/0.44         = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.22/0.44      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.44  thf(d10_xboole_0, axiom,
% 0.22/0.44    (![A:$i,B:$i]:
% 0.22/0.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.44  thf('4', plain,
% 0.22/0.44      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.44  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.44      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.44  thf(t37_xboole_1, axiom,
% 0.22/0.44    (![A:$i,B:$i]:
% 0.22/0.44     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.44  thf('6', plain,
% 0.22/0.44      (![X3 : $i, X5 : $i]:
% 0.22/0.44         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.22/0.44      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.22/0.44  thf('7', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.44      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.44  thf('8', plain,
% 0.22/0.44      (((k1_xboole_0) = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.22/0.44      inference('demod', [status(thm)], ['3', '7'])).
% 0.22/0.44  thf('9', plain,
% 0.22/0.44      (![X3 : $i, X4 : $i]:
% 0.22/0.44         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.22/0.44      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.22/0.44  thf('10', plain,
% 0.22/0.44      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.44        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.22/0.44      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.44  thf('11', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.22/0.44      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.44  thf(t38_zfmisc_1, axiom,
% 0.22/0.44    (![A:$i,B:$i,C:$i]:
% 0.22/0.44     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.22/0.44       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.22/0.44  thf('12', plain,
% 0.22/0.44      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.44         ((r2_hidden @ X8 @ X9) | ~ (r1_tarski @ (k2_tarski @ X8 @ X10) @ X9))),
% 0.22/0.44      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.44  thf('13', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.22/0.44      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.44  thf('14', plain, ($false), inference('demod', [status(thm)], ['0', '13'])).
% 0.22/0.44  
% 0.22/0.44  % SZS output end Refutation
% 0.22/0.44  
% 0.22/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
