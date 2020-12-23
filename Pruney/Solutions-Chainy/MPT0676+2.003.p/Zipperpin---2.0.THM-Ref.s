%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.peIOXY2TgO

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  197 ( 223 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X5 @ X6 ) @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t158_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k9_relat_1 @ X8 @ X9 ) @ ( k9_relat_1 @ X7 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X7 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t158_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X3 ) @ ( k9_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X3 ) @ ( k9_relat_1 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X3 ) @ ( k9_relat_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X3 ) @ ( k9_relat_1 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf(t120_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( r1_tarski @ ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) @ ( k9_relat_1 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( r1_tarski @ ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) @ ( k9_relat_1 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t120_funct_1])).

thf('10',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['11','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.peIOXY2TgO
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 14 iterations in 0.014s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.44  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.44  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.44  thf(d10_xboole_0, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.44  thf('0', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.44  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.44      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.44  thf(dt_k8_relat_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      (![X3 : $i, X4 : $i]:
% 0.20/0.44         ((v1_relat_1 @ (k8_relat_1 @ X3 @ X4)) | ~ (v1_relat_1 @ X4))),
% 0.20/0.44      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.20/0.44  thf(t117_relat_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.20/0.44  thf('3', plain,
% 0.20/0.44      (![X5 : $i, X6 : $i]:
% 0.20/0.44         ((r1_tarski @ (k8_relat_1 @ X5 @ X6) @ X6) | ~ (v1_relat_1 @ X6))),
% 0.20/0.44      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.20/0.44  thf(t158_relat_1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( v1_relat_1 @ C ) =>
% 0.20/0.44       ( ![D:$i]:
% 0.20/0.44         ( ( v1_relat_1 @ D ) =>
% 0.20/0.44           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.20/0.44             ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.20/0.44  thf('4', plain,
% 0.20/0.44      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.44         (~ (v1_relat_1 @ X7)
% 0.20/0.44          | (r1_tarski @ (k9_relat_1 @ X8 @ X9) @ (k9_relat_1 @ X7 @ X10))
% 0.20/0.44          | ~ (r1_tarski @ X8 @ X7)
% 0.20/0.44          | ~ (r1_tarski @ X9 @ X10)
% 0.20/0.44          | ~ (v1_relat_1 @ X8))),
% 0.20/0.44      inference('cnf', [status(esa)], [t158_relat_1])).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.44         (~ (v1_relat_1 @ X0)
% 0.20/0.44          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.44          | ~ (r1_tarski @ X3 @ X2)
% 0.20/0.44          | (r1_tarski @ (k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X3) @ 
% 0.20/0.44             (k9_relat_1 @ X0 @ X2))
% 0.20/0.44          | ~ (v1_relat_1 @ X0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.44         ((r1_tarski @ (k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X3) @ 
% 0.20/0.44           (k9_relat_1 @ X0 @ X2))
% 0.20/0.44          | ~ (r1_tarski @ X3 @ X2)
% 0.20/0.44          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.44          | ~ (v1_relat_1 @ X0))),
% 0.20/0.44      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.44         (~ (v1_relat_1 @ X0)
% 0.20/0.44          | ~ (v1_relat_1 @ X0)
% 0.20/0.44          | ~ (r1_tarski @ X3 @ X2)
% 0.20/0.44          | (r1_tarski @ (k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X3) @ 
% 0.20/0.44             (k9_relat_1 @ X0 @ X2)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['2', '6'])).
% 0.20/0.44  thf('8', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.44         ((r1_tarski @ (k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X3) @ 
% 0.20/0.44           (k9_relat_1 @ X0 @ X2))
% 0.20/0.44          | ~ (r1_tarski @ X3 @ X2)
% 0.20/0.44          | ~ (v1_relat_1 @ X0))),
% 0.20/0.44      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         (~ (v1_relat_1 @ X1)
% 0.20/0.44          | (r1_tarski @ (k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0) @ 
% 0.20/0.44             (k9_relat_1 @ X1 @ X0)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['1', '8'])).
% 0.20/0.44  thf(t120_funct_1, conjecture,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.44       ( r1_tarski @
% 0.20/0.44         ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) @ ( k9_relat_1 @ C @ B ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.44        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.44          ( r1_tarski @
% 0.20/0.44            ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) @ 
% 0.20/0.44            ( k9_relat_1 @ C @ B ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t120_funct_1])).
% 0.20/0.44  thf('10', plain,
% 0.20/0.44      (~ (r1_tarski @ (k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B) @ 
% 0.20/0.44          (k9_relat_1 @ sk_C @ sk_B))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('11', plain, (~ (v1_relat_1 @ sk_C)),
% 0.20/0.44      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.44  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('13', plain, ($false), inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
