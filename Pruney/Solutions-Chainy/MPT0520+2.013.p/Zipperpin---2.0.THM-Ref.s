%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XwMbtftRWM

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:35 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  77 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :   18
%              Number of atoms          :  581 ( 839 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

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
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t120_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
         => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t120_relat_1])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t115_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ ( k2_relat_1 @ X21 ) )
      | ( r2_hidden @ X19 @ ( k2_relat_1 @ ( k8_relat_1 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t115_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ sk_B ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ sk_B ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,
    ( ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_A @ X0 @ sk_A ) @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_D @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('24',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k2_relat_1 @ ( k8_relat_1 @ X20 @ X21 ) ) )
      | ( r2_hidden @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t115_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X2 @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('30',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XwMbtftRWM
% 0.14/0.37  % Computer   : n012.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 18:00:37 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 1.20/1.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.20/1.42  % Solved by: fo/fo7.sh
% 1.20/1.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.42  % done 1302 iterations in 0.942s
% 1.20/1.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.20/1.42  % SZS output start Refutation
% 1.20/1.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.20/1.42  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.20/1.42  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.20/1.42  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.20/1.42  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.20/1.42  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.20/1.42  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.20/1.42  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.20/1.42  thf(d4_xboole_0, axiom,
% 1.20/1.42    (![A:$i,B:$i,C:$i]:
% 1.20/1.42     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.20/1.42       ( ![D:$i]:
% 1.20/1.42         ( ( r2_hidden @ D @ C ) <=>
% 1.20/1.42           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.20/1.42  thf('0', plain,
% 1.20/1.42      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.20/1.42         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.20/1.42          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 1.20/1.42          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.20/1.42      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.20/1.42  thf('1', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i]:
% 1.20/1.42         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.20/1.42          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.20/1.42      inference('eq_fact', [status(thm)], ['0'])).
% 1.20/1.42  thf(d3_tarski, axiom,
% 1.20/1.42    (![A:$i,B:$i]:
% 1.20/1.42     ( ( r1_tarski @ A @ B ) <=>
% 1.20/1.42       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.20/1.42  thf('2', plain,
% 1.20/1.42      (![X1 : $i, X3 : $i]:
% 1.20/1.42         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.20/1.42      inference('cnf', [status(esa)], [d3_tarski])).
% 1.20/1.42  thf('3', plain,
% 1.20/1.42      (![X1 : $i, X3 : $i]:
% 1.20/1.42         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.20/1.42      inference('cnf', [status(esa)], [d3_tarski])).
% 1.20/1.42  thf(t120_relat_1, conjecture,
% 1.20/1.42    (![A:$i,B:$i]:
% 1.20/1.42     ( ( v1_relat_1 @ B ) =>
% 1.20/1.42       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.20/1.42         ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) = ( A ) ) ) ))).
% 1.20/1.42  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.42    (~( ![A:$i,B:$i]:
% 1.20/1.42        ( ( v1_relat_1 @ B ) =>
% 1.20/1.42          ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.20/1.42            ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) = ( A ) ) ) ) )),
% 1.20/1.42    inference('cnf.neg', [status(esa)], [t120_relat_1])).
% 1.20/1.42  thf('4', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('5', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.42         (~ (r2_hidden @ X0 @ X1)
% 1.20/1.42          | (r2_hidden @ X0 @ X2)
% 1.20/1.42          | ~ (r1_tarski @ X1 @ X2))),
% 1.20/1.42      inference('cnf', [status(esa)], [d3_tarski])).
% 1.20/1.42  thf('6', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((r2_hidden @ X0 @ (k2_relat_1 @ sk_B)) | ~ (r2_hidden @ X0 @ sk_A))),
% 1.20/1.42      inference('sup-', [status(thm)], ['4', '5'])).
% 1.20/1.42  thf('7', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((r1_tarski @ sk_A @ X0)
% 1.20/1.42          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['3', '6'])).
% 1.20/1.42  thf(t115_relat_1, axiom,
% 1.20/1.42    (![A:$i,B:$i,C:$i]:
% 1.20/1.42     ( ( v1_relat_1 @ C ) =>
% 1.20/1.42       ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) <=>
% 1.20/1.42         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ C ) ) ) ) ))).
% 1.20/1.42  thf('8', plain,
% 1.20/1.42      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.20/1.42         (~ (r2_hidden @ X19 @ X20)
% 1.20/1.42          | ~ (r2_hidden @ X19 @ (k2_relat_1 @ X21))
% 1.20/1.42          | (r2_hidden @ X19 @ (k2_relat_1 @ (k8_relat_1 @ X20 @ X21)))
% 1.20/1.42          | ~ (v1_relat_1 @ X21))),
% 1.20/1.42      inference('cnf', [status(esa)], [t115_relat_1])).
% 1.20/1.42  thf('9', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i]:
% 1.20/1.42         ((r1_tarski @ sk_A @ X0)
% 1.20/1.42          | ~ (v1_relat_1 @ sk_B)
% 1.20/1.42          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 1.20/1.42             (k2_relat_1 @ (k8_relat_1 @ X1 @ sk_B)))
% 1.20/1.42          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1))),
% 1.20/1.42      inference('sup-', [status(thm)], ['7', '8'])).
% 1.20/1.42  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('11', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i]:
% 1.20/1.42         ((r1_tarski @ sk_A @ X0)
% 1.20/1.42          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 1.20/1.42             (k2_relat_1 @ (k8_relat_1 @ X1 @ sk_B)))
% 1.20/1.42          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1))),
% 1.20/1.42      inference('demod', [status(thm)], ['9', '10'])).
% 1.20/1.42  thf('12', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((r1_tarski @ sk_A @ X0)
% 1.20/1.42          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 1.20/1.42             (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))
% 1.20/1.42          | (r1_tarski @ sk_A @ X0))),
% 1.20/1.42      inference('sup-', [status(thm)], ['2', '11'])).
% 1.20/1.42  thf('13', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 1.20/1.42           (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))
% 1.20/1.42          | (r1_tarski @ sk_A @ X0))),
% 1.20/1.42      inference('simplify', [status(thm)], ['12'])).
% 1.20/1.42  thf('14', plain,
% 1.20/1.42      (![X1 : $i, X3 : $i]:
% 1.20/1.42         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.20/1.42      inference('cnf', [status(esa)], [d3_tarski])).
% 1.20/1.42  thf('15', plain,
% 1.20/1.42      (((r1_tarski @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))
% 1.20/1.42        | (r1_tarski @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))))),
% 1.20/1.42      inference('sup-', [status(thm)], ['13', '14'])).
% 1.20/1.42  thf('16', plain,
% 1.20/1.42      ((r1_tarski @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))),
% 1.20/1.42      inference('simplify', [status(thm)], ['15'])).
% 1.20/1.42  thf('17', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.42         (~ (r2_hidden @ X0 @ X1)
% 1.20/1.42          | (r2_hidden @ X0 @ X2)
% 1.20/1.42          | ~ (r1_tarski @ X1 @ X2))),
% 1.20/1.42      inference('cnf', [status(esa)], [d3_tarski])).
% 1.20/1.42  thf('18', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((r2_hidden @ X0 @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))
% 1.20/1.42          | ~ (r2_hidden @ X0 @ sk_A))),
% 1.20/1.42      inference('sup-', [status(thm)], ['16', '17'])).
% 1.20/1.42  thf('19', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         (((sk_A) = (k3_xboole_0 @ sk_A @ X0))
% 1.20/1.42          | (r2_hidden @ (sk_D @ sk_A @ X0 @ sk_A) @ 
% 1.20/1.42             (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))))),
% 1.20/1.42      inference('sup-', [status(thm)], ['1', '18'])).
% 1.20/1.42  thf('20', plain,
% 1.20/1.42      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.20/1.42         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.20/1.42          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.20/1.42          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 1.20/1.42          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.20/1.42      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.20/1.42  thf('21', plain,
% 1.20/1.42      ((((sk_A)
% 1.20/1.42          = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))))
% 1.20/1.42        | ~ (r2_hidden @ 
% 1.20/1.42             (sk_D @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 1.20/1.42             sk_A)
% 1.20/1.42        | ~ (r2_hidden @ 
% 1.20/1.42             (sk_D @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 1.20/1.42             sk_A)
% 1.20/1.42        | ((sk_A)
% 1.20/1.42            = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))))),
% 1.20/1.42      inference('sup-', [status(thm)], ['19', '20'])).
% 1.20/1.42  thf('22', plain,
% 1.20/1.42      ((~ (r2_hidden @ 
% 1.20/1.42           (sk_D @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) @ sk_A) @ 
% 1.20/1.42           sk_A)
% 1.20/1.42        | ((sk_A)
% 1.20/1.42            = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)))))),
% 1.20/1.42      inference('simplify', [status(thm)], ['21'])).
% 1.20/1.42  thf('23', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i]:
% 1.20/1.42         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.20/1.42          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.20/1.42      inference('eq_fact', [status(thm)], ['0'])).
% 1.20/1.42  thf('24', plain,
% 1.20/1.42      (((sk_A)
% 1.20/1.42         = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B))))),
% 1.20/1.42      inference('clc', [status(thm)], ['22', '23'])).
% 1.20/1.42  thf('25', plain,
% 1.20/1.42      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.20/1.42         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.20/1.42          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.20/1.42          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.20/1.42      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.20/1.42  thf('26', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i]:
% 1.20/1.42         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.20/1.42          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.20/1.42      inference('eq_fact', [status(thm)], ['25'])).
% 1.20/1.42  thf('27', plain,
% 1.20/1.42      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.20/1.42         (~ (r2_hidden @ X19 @ (k2_relat_1 @ (k8_relat_1 @ X20 @ X21)))
% 1.20/1.42          | (r2_hidden @ X19 @ X20)
% 1.20/1.42          | ~ (v1_relat_1 @ X21))),
% 1.20/1.42      inference('cnf', [status(esa)], [t115_relat_1])).
% 1.20/1.42  thf('28', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.42         (((k2_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.20/1.42            = (k3_xboole_0 @ X2 @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0))))
% 1.20/1.42          | ~ (v1_relat_1 @ X0)
% 1.20/1.42          | (r2_hidden @ 
% 1.20/1.42             (sk_D @ (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ 
% 1.20/1.42              (k2_relat_1 @ (k8_relat_1 @ X1 @ X0)) @ X2) @ 
% 1.20/1.42             X1))),
% 1.20/1.42      inference('sup-', [status(thm)], ['26', '27'])).
% 1.20/1.42  thf('29', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i]:
% 1.20/1.42         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.20/1.42          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.20/1.42      inference('eq_fact', [status(thm)], ['25'])).
% 1.20/1.42  thf('30', plain,
% 1.20/1.42      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.20/1.42         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.20/1.42          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.20/1.42          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 1.20/1.42          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.20/1.42      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.20/1.42  thf('31', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i]:
% 1.20/1.42         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.20/1.42          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.20/1.42          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.20/1.42          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['29', '30'])).
% 1.20/1.42  thf('32', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i]:
% 1.20/1.42         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.20/1.42          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.20/1.42          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.20/1.42      inference('simplify', [status(thm)], ['31'])).
% 1.20/1.42  thf('33', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i]:
% 1.20/1.42         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.20/1.42          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.20/1.42      inference('eq_fact', [status(thm)], ['25'])).
% 1.20/1.42  thf('34', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i]:
% 1.20/1.42         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.20/1.42          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.20/1.42      inference('clc', [status(thm)], ['32', '33'])).
% 1.20/1.42  thf('35', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i]:
% 1.20/1.42         (~ (v1_relat_1 @ X1)
% 1.20/1.42          | ((k2_relat_1 @ (k8_relat_1 @ X0 @ X1))
% 1.20/1.42              = (k3_xboole_0 @ X0 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1))))
% 1.20/1.42          | ((k2_relat_1 @ (k8_relat_1 @ X0 @ X1))
% 1.20/1.42              = (k3_xboole_0 @ X0 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)))))),
% 1.20/1.42      inference('sup-', [status(thm)], ['28', '34'])).
% 1.20/1.42  thf('36', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i]:
% 1.20/1.42         (((k2_relat_1 @ (k8_relat_1 @ X0 @ X1))
% 1.20/1.42            = (k3_xboole_0 @ X0 @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1))))
% 1.20/1.42          | ~ (v1_relat_1 @ X1))),
% 1.20/1.42      inference('simplify', [status(thm)], ['35'])).
% 1.20/1.42  thf('37', plain,
% 1.20/1.42      ((((k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) = (sk_A))
% 1.20/1.42        | ~ (v1_relat_1 @ sk_B))),
% 1.20/1.42      inference('sup+', [status(thm)], ['24', '36'])).
% 1.20/1.42  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('39', plain, (((k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) = (sk_A))),
% 1.20/1.42      inference('demod', [status(thm)], ['37', '38'])).
% 1.20/1.42  thf('40', plain, (((k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) != (sk_A))),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('41', plain, ($false),
% 1.20/1.42      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 1.20/1.42  
% 1.20/1.42  % SZS output end Refutation
% 1.20/1.42  
% 1.20/1.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
