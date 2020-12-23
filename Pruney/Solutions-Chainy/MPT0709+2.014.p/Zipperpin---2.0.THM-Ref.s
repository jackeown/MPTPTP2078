%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K47bWZEzeK

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:07 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   54 (  65 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  422 ( 601 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X30 @ X31 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k9_relat_1 @ X40 @ ( k10_relat_1 @ X40 @ X39 ) )
        = ( k3_xboole_0 @ X39 @ ( k9_relat_1 @ X40 @ ( k1_relat_1 @ X40 ) ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(t157_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r1_tarski @ X41 @ X42 )
      | ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v2_funct_1 @ X43 )
      | ~ ( r1_tarski @ X41 @ ( k1_relat_1 @ X43 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X43 @ X41 ) @ ( k9_relat_1 @ X43 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('17',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X35 @ ( k1_relat_1 @ X36 ) )
      | ( r1_tarski @ X35 @ ( k10_relat_1 @ X36 @ ( k9_relat_1 @ X36 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['26','27','28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K47bWZEzeK
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.05/1.26  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.26  % Solved by: fo/fo7.sh
% 1.05/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.26  % done 1362 iterations in 0.805s
% 1.05/1.26  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.26  % SZS output start Refutation
% 1.05/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.26  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.05/1.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.26  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.05/1.26  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.05/1.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.26  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.26  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.05/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.26  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.05/1.26  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.05/1.26  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.05/1.26  thf(t167_relat_1, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( v1_relat_1 @ B ) =>
% 1.05/1.26       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.05/1.26  thf('0', plain,
% 1.05/1.26      (![X30 : $i, X31 : $i]:
% 1.05/1.26         ((r1_tarski @ (k10_relat_1 @ X30 @ X31) @ (k1_relat_1 @ X30))
% 1.05/1.26          | ~ (v1_relat_1 @ X30))),
% 1.05/1.26      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.05/1.26  thf(t148_funct_1, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.05/1.26       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 1.05/1.26         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 1.05/1.26  thf('1', plain,
% 1.05/1.26      (![X39 : $i, X40 : $i]:
% 1.05/1.26         (((k9_relat_1 @ X40 @ (k10_relat_1 @ X40 @ X39))
% 1.05/1.26            = (k3_xboole_0 @ X39 @ (k9_relat_1 @ X40 @ (k1_relat_1 @ X40))))
% 1.05/1.26          | ~ (v1_funct_1 @ X40)
% 1.05/1.26          | ~ (v1_relat_1 @ X40))),
% 1.05/1.26      inference('cnf', [status(esa)], [t148_funct_1])).
% 1.05/1.26  thf(t48_xboole_1, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.05/1.26  thf('2', plain,
% 1.05/1.26      (![X17 : $i, X18 : $i]:
% 1.05/1.26         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.05/1.26           = (k3_xboole_0 @ X17 @ X18))),
% 1.05/1.26      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.05/1.26  thf(d3_tarski, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( r1_tarski @ A @ B ) <=>
% 1.05/1.26       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.05/1.26  thf('3', plain,
% 1.05/1.26      (![X1 : $i, X3 : $i]:
% 1.05/1.26         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.05/1.26      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.26  thf(d5_xboole_0, axiom,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.05/1.26       ( ![D:$i]:
% 1.05/1.26         ( ( r2_hidden @ D @ C ) <=>
% 1.05/1.26           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.05/1.26  thf('4', plain,
% 1.05/1.26      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.05/1.26         (~ (r2_hidden @ X8 @ X7)
% 1.05/1.26          | (r2_hidden @ X8 @ X5)
% 1.05/1.26          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 1.05/1.26      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.05/1.26  thf('5', plain,
% 1.05/1.26      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.05/1.26         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 1.05/1.26      inference('simplify', [status(thm)], ['4'])).
% 1.05/1.26  thf('6', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.26         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.05/1.26          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 1.05/1.26      inference('sup-', [status(thm)], ['3', '5'])).
% 1.05/1.26  thf('7', plain,
% 1.05/1.26      (![X1 : $i, X3 : $i]:
% 1.05/1.26         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.05/1.26      inference('cnf', [status(esa)], [d3_tarski])).
% 1.05/1.26  thf('8', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.05/1.26          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['6', '7'])).
% 1.05/1.26  thf('9', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 1.05/1.26      inference('simplify', [status(thm)], ['8'])).
% 1.05/1.26  thf('10', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.05/1.26      inference('sup+', [status(thm)], ['2', '9'])).
% 1.05/1.26  thf('11', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         ((r1_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 1.05/1.26          | ~ (v1_relat_1 @ X1)
% 1.05/1.26          | ~ (v1_funct_1 @ X1))),
% 1.05/1.26      inference('sup+', [status(thm)], ['1', '10'])).
% 1.05/1.26  thf(t157_funct_1, axiom,
% 1.05/1.26    (![A:$i,B:$i,C:$i]:
% 1.05/1.26     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.05/1.26       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 1.05/1.26           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 1.05/1.26         ( r1_tarski @ A @ B ) ) ))).
% 1.05/1.26  thf('12', plain,
% 1.05/1.26      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.05/1.26         ((r1_tarski @ X41 @ X42)
% 1.05/1.26          | ~ (v1_relat_1 @ X43)
% 1.05/1.26          | ~ (v1_funct_1 @ X43)
% 1.05/1.26          | ~ (v2_funct_1 @ X43)
% 1.05/1.26          | ~ (r1_tarski @ X41 @ (k1_relat_1 @ X43))
% 1.05/1.26          | ~ (r1_tarski @ (k9_relat_1 @ X43 @ X41) @ (k9_relat_1 @ X43 @ X42)))),
% 1.05/1.26      inference('cnf', [status(esa)], [t157_funct_1])).
% 1.05/1.26  thf('13', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (v1_funct_1 @ X1)
% 1.05/1.26          | ~ (v1_relat_1 @ X1)
% 1.05/1.26          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ 
% 1.05/1.26               (k1_relat_1 @ X1))
% 1.05/1.26          | ~ (v2_funct_1 @ X1)
% 1.05/1.26          | ~ (v1_funct_1 @ X1)
% 1.05/1.26          | ~ (v1_relat_1 @ X1)
% 1.05/1.26          | (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))),
% 1.05/1.26      inference('sup-', [status(thm)], ['11', '12'])).
% 1.05/1.26  thf('14', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         ((r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 1.05/1.26          | ~ (v2_funct_1 @ X1)
% 1.05/1.26          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ 
% 1.05/1.26               (k1_relat_1 @ X1))
% 1.05/1.26          | ~ (v1_relat_1 @ X1)
% 1.05/1.26          | ~ (v1_funct_1 @ X1))),
% 1.05/1.26      inference('simplify', [status(thm)], ['13'])).
% 1.05/1.26  thf('15', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         (~ (v1_relat_1 @ X0)
% 1.05/1.26          | ~ (v1_funct_1 @ X0)
% 1.05/1.26          | ~ (v1_relat_1 @ X0)
% 1.05/1.26          | ~ (v2_funct_1 @ X0)
% 1.05/1.26          | (r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)) @ X1))),
% 1.05/1.26      inference('sup-', [status(thm)], ['0', '14'])).
% 1.05/1.26  thf('16', plain,
% 1.05/1.26      (![X0 : $i, X1 : $i]:
% 1.05/1.26         ((r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ X1)) @ X1)
% 1.05/1.26          | ~ (v2_funct_1 @ X0)
% 1.05/1.26          | ~ (v1_funct_1 @ X0)
% 1.05/1.26          | ~ (v1_relat_1 @ X0))),
% 1.05/1.26      inference('simplify', [status(thm)], ['15'])).
% 1.05/1.26  thf(t164_funct_1, conjecture,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.05/1.26       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.05/1.26         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.05/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.26    (~( ![A:$i,B:$i]:
% 1.05/1.26        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.05/1.26          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.05/1.26            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 1.05/1.26    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 1.05/1.26  thf('17', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf(t146_funct_1, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( v1_relat_1 @ B ) =>
% 1.05/1.26       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.05/1.26         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.05/1.26  thf('18', plain,
% 1.05/1.26      (![X35 : $i, X36 : $i]:
% 1.05/1.26         (~ (r1_tarski @ X35 @ (k1_relat_1 @ X36))
% 1.05/1.26          | (r1_tarski @ X35 @ (k10_relat_1 @ X36 @ (k9_relat_1 @ X36 @ X35)))
% 1.05/1.26          | ~ (v1_relat_1 @ X36))),
% 1.05/1.26      inference('cnf', [status(esa)], [t146_funct_1])).
% 1.05/1.26  thf('19', plain,
% 1.05/1.26      ((~ (v1_relat_1 @ sk_B)
% 1.05/1.26        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 1.05/1.26      inference('sup-', [status(thm)], ['17', '18'])).
% 1.05/1.26  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('21', plain,
% 1.05/1.26      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.05/1.26      inference('demod', [status(thm)], ['19', '20'])).
% 1.05/1.26  thf(d10_xboole_0, axiom,
% 1.05/1.26    (![A:$i,B:$i]:
% 1.05/1.26     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.05/1.26  thf('22', plain,
% 1.05/1.26      (![X10 : $i, X12 : $i]:
% 1.05/1.26         (((X10) = (X12))
% 1.05/1.26          | ~ (r1_tarski @ X12 @ X10)
% 1.05/1.26          | ~ (r1_tarski @ X10 @ X12))),
% 1.05/1.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.05/1.26  thf('23', plain,
% 1.05/1.26      ((~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 1.05/1.26        | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 1.05/1.26      inference('sup-', [status(thm)], ['21', '22'])).
% 1.05/1.26  thf('24', plain,
% 1.05/1.26      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('25', plain,
% 1.05/1.26      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 1.05/1.26      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 1.05/1.26  thf('26', plain,
% 1.05/1.26      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ~ (v2_funct_1 @ sk_B))),
% 1.05/1.26      inference('sup-', [status(thm)], ['16', '25'])).
% 1.05/1.26  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('29', plain, ((v2_funct_1 @ sk_B)),
% 1.05/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.26  thf('30', plain, ($false),
% 1.05/1.26      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 1.05/1.26  
% 1.05/1.26  % SZS output end Refutation
% 1.05/1.26  
% 1.05/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
