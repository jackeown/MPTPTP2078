%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RqSHWstM8P

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:19 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   59 (  77 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  385 ( 546 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X32
       != ( k1_wellord1 @ X31 @ X30 ) )
      | ( r2_hidden @ ( k4_tarski @ X33 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('2',plain,(
    ! [X30: $i,X31: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( r2_hidden @ X33 @ ( k1_wellord1 @ X31 @ X30 ) )
      | ( r2_hidden @ ( k4_tarski @ X33 @ X30 ) @ X31 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X21 )
      | ( r2_hidden @ X20 @ X22 )
      | ( X22
       != ( k2_relat_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k2_relat_1 @ X21 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X21 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_wellord1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('8',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24
        = ( k2_relat_1 @ X21 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X24 @ X21 ) @ ( sk_C_1 @ X24 @ X21 ) ) @ X21 )
      | ( r2_hidden @ ( sk_C_1 @ X24 @ X21 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( k4_tarski @ ( sk_D_1 @ X1 @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('16',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_wellord1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X26: $i] :
      ( ( ( k3_relat_1 @ X26 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X26 ) @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X26: $i] :
      ( ( ( k3_relat_1 @ X26 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X26 ) @ ( k1_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t2_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) )
        | ( ( k1_wellord1 @ B @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) )
          | ( ( k1_wellord1 @ B @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_wellord1])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k1_wellord1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_wellord1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ( k1_wellord1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RqSHWstM8P
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:38:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 332 iterations in 0.171s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.62  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.62  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.38/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.38/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.62  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(d3_tarski, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      (![X3 : $i, X5 : $i]:
% 0.38/0.62         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.62  thf(d1_wellord1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ A ) =>
% 0.38/0.62       ( ![B:$i,C:$i]:
% 0.38/0.62         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.38/0.62           ( ![D:$i]:
% 0.38/0.62             ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.62               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.62         (((X32) != (k1_wellord1 @ X31 @ X30))
% 0.38/0.62          | (r2_hidden @ (k4_tarski @ X33 @ X30) @ X31)
% 0.38/0.62          | ~ (r2_hidden @ X33 @ X32)
% 0.38/0.62          | ~ (v1_relat_1 @ X31))),
% 0.38/0.62      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (![X30 : $i, X31 : $i, X33 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X31)
% 0.38/0.62          | ~ (r2_hidden @ X33 @ (k1_wellord1 @ X31 @ X30))
% 0.38/0.62          | (r2_hidden @ (k4_tarski @ X33 @ X30) @ X31))),
% 0.38/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         ((r1_tarski @ (k1_wellord1 @ X1 @ X0) @ X2)
% 0.38/0.62          | (r2_hidden @ 
% 0.38/0.62             (k4_tarski @ (sk_C @ X2 @ (k1_wellord1 @ X1 @ X0)) @ X0) @ X1)
% 0.38/0.62          | ~ (v1_relat_1 @ X1))),
% 0.38/0.62      inference('sup-', [status(thm)], ['0', '2'])).
% 0.38/0.62  thf(d5_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.38/0.62       ( ![C:$i]:
% 0.38/0.62         ( ( r2_hidden @ C @ B ) <=>
% 0.38/0.62           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.38/0.62  thf('4', plain,
% 0.38/0.62      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.62         (~ (r2_hidden @ (k4_tarski @ X19 @ X20) @ X21)
% 0.38/0.62          | (r2_hidden @ X20 @ X22)
% 0.38/0.62          | ((X22) != (k2_relat_1 @ X21)))),
% 0.38/0.62      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.62         ((r2_hidden @ X20 @ (k2_relat_1 @ X21))
% 0.38/0.62          | ~ (r2_hidden @ (k4_tarski @ X19 @ X20) @ X21))),
% 0.38/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | (r1_tarski @ (k1_wellord1 @ X0 @ X1) @ X2)
% 0.38/0.62          | (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['3', '5'])).
% 0.38/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.62  thf('7', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.38/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (![X21 : $i, X24 : $i]:
% 0.38/0.62         (((X24) = (k2_relat_1 @ X21))
% 0.38/0.62          | (r2_hidden @ 
% 0.38/0.62             (k4_tarski @ (sk_D_1 @ X24 @ X21) @ (sk_C_1 @ X24 @ X21)) @ X21)
% 0.38/0.62          | (r2_hidden @ (sk_C_1 @ X24 @ X21) @ X24))),
% 0.38/0.62      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.38/0.62  thf(t7_ordinal1, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.62  thf('9', plain,
% 0.38/0.62      (![X27 : $i, X28 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 0.38/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.38/0.62          | ((X1) = (k2_relat_1 @ X0))
% 0.38/0.62          | ~ (r1_tarski @ X0 @ 
% 0.38/0.62               (k4_tarski @ (sk_D_1 @ X1 @ X0) @ (sk_C_1 @ X1 @ X0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.38/0.62          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['7', '10'])).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      (![X27 : $i, X28 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 0.38/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.38/0.62          | ~ (r1_tarski @ X0 @ (sk_C_1 @ X0 @ k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.62  thf('14', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.38/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.62  thf('15', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.38/0.62          | ~ (r1_tarski @ X0 @ (sk_C_1 @ X0 @ k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.62  thf('16', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((X0) = (k1_xboole_0))
% 0.38/0.62          | ~ (r1_tarski @ X0 @ (sk_C_1 @ X0 @ k1_xboole_0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['13', '16'])).
% 0.38/0.62  thf('18', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 0.38/0.62          | ~ (v1_relat_1 @ X1)
% 0.38/0.62          | ((k1_wellord1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['6', '17'])).
% 0.38/0.62  thf(d6_relat_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ A ) =>
% 0.38/0.62       ( ( k3_relat_1 @ A ) =
% 0.38/0.62         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      (![X26 : $i]:
% 0.38/0.62         (((k3_relat_1 @ X26)
% 0.38/0.62            = (k2_xboole_0 @ (k1_relat_1 @ X26) @ (k2_relat_1 @ X26)))
% 0.38/0.62          | ~ (v1_relat_1 @ X26))),
% 0.38/0.62      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.38/0.62  thf(commutativity_k2_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (![X26 : $i]:
% 0.38/0.62         (((k3_relat_1 @ X26)
% 0.38/0.62            = (k2_xboole_0 @ (k2_relat_1 @ X26) @ (k1_relat_1 @ X26)))
% 0.38/0.62          | ~ (v1_relat_1 @ X26))),
% 0.38/0.62      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.62  thf(t7_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.38/0.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['21', '22'])).
% 0.38/0.62  thf('24', plain,
% 0.38/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X2 @ X3)
% 0.38/0.62          | (r2_hidden @ X2 @ X4)
% 0.38/0.62          | ~ (r1_tarski @ X3 @ X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | (r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.38/0.62          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((k1_wellord1 @ X0 @ X1) = (k1_xboole_0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | (r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['18', '25'])).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ((k1_wellord1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.38/0.62  thf(t2_wellord1, conjecture,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ B ) =>
% 0.38/0.62       ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) ) | 
% 0.38/0.62         ( ( k1_wellord1 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i,B:$i]:
% 0.38/0.62        ( ( v1_relat_1 @ B ) =>
% 0.38/0.62          ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) ) | 
% 0.38/0.62            ( ( k1_wellord1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t2_wellord1])).
% 0.38/0.62  thf('28', plain, (~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_B))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      ((((k1_wellord1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('31', plain, (((k1_wellord1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.62  thf('32', plain, (((k1_wellord1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('33', plain, ($false),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
