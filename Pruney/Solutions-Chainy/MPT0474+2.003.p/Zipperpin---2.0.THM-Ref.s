%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0UljGwfJJ3

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:54 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 117 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  336 ( 925 expanded)
%              Number of equality atoms :   26 (  72 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('11',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('13',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(d7_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( B
              = ( k4_relat_1 @ A ) )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X18 @ X19 ) @ ( sk_D_3 @ X18 @ X19 ) ) @ X18 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X18 @ X19 ) @ ( sk_C_2 @ X18 @ X19 ) ) @ X19 )
      | ( X18
        = ( k4_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( X0
        = ( k4_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X0 @ X1 ) @ ( sk_C_2 @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0
        = ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k4_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k4_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','30'])).

thf(t66_relat_1,conjecture,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t66_relat_1])).

thf('32',plain,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0UljGwfJJ3
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:32:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.14/1.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.14/1.38  % Solved by: fo/fo7.sh
% 1.14/1.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.38  % done 1345 iterations in 0.877s
% 1.14/1.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.14/1.38  % SZS output start Refutation
% 1.14/1.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.14/1.38  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.14/1.38  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.14/1.38  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.14/1.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.14/1.38  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 1.14/1.38  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.14/1.38  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.14/1.38  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.14/1.38  thf(sk_C_type, type, sk_C: $i > $i).
% 1.14/1.38  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.14/1.38  thf(d5_xboole_0, axiom,
% 1.14/1.38    (![A:$i,B:$i,C:$i]:
% 1.14/1.38     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.14/1.38       ( ![D:$i]:
% 1.14/1.38         ( ( r2_hidden @ D @ C ) <=>
% 1.14/1.38           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.14/1.38  thf('0', plain,
% 1.14/1.38      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.14/1.38         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.14/1.38          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.14/1.38          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.14/1.38      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.14/1.38  thf(t4_boole, axiom,
% 1.14/1.38    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.14/1.38  thf('1', plain,
% 1.14/1.38      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.14/1.38      inference('cnf', [status(esa)], [t4_boole])).
% 1.14/1.38  thf('2', plain,
% 1.14/1.38      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.14/1.38         (~ (r2_hidden @ X4 @ X3)
% 1.14/1.38          | ~ (r2_hidden @ X4 @ X2)
% 1.14/1.38          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.14/1.38      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.14/1.38  thf('3', plain,
% 1.14/1.38      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.14/1.38         (~ (r2_hidden @ X4 @ X2)
% 1.14/1.38          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.14/1.38      inference('simplify', [status(thm)], ['2'])).
% 1.14/1.38  thf('4', plain,
% 1.14/1.38      (![X0 : $i, X1 : $i]:
% 1.14/1.38         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 1.14/1.38      inference('sup-', [status(thm)], ['1', '3'])).
% 1.14/1.38  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.14/1.38      inference('condensation', [status(thm)], ['4'])).
% 1.14/1.38  thf('6', plain,
% 1.14/1.38      (![X0 : $i, X1 : $i]:
% 1.14/1.38         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 1.14/1.38          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.14/1.38      inference('sup-', [status(thm)], ['0', '5'])).
% 1.14/1.38  thf('7', plain,
% 1.14/1.38      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.14/1.38         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.14/1.38          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.14/1.38          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.14/1.38      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.14/1.38  thf('8', plain,
% 1.14/1.38      (![X0 : $i]:
% 1.14/1.38         (((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))
% 1.14/1.38          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 1.14/1.38          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 1.14/1.38      inference('sup-', [status(thm)], ['6', '7'])).
% 1.14/1.38  thf('9', plain,
% 1.14/1.38      (![X0 : $i]:
% 1.14/1.38         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 1.14/1.38          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 1.14/1.38      inference('simplify', [status(thm)], ['8'])).
% 1.14/1.38  thf('10', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.14/1.38      inference('condensation', [status(thm)], ['4'])).
% 1.14/1.38  thf('11', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.14/1.38      inference('clc', [status(thm)], ['9', '10'])).
% 1.14/1.38  thf(cc1_relat_1, axiom,
% 1.14/1.38    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 1.14/1.38  thf('12', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 1.14/1.38      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.14/1.38  thf('13', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 1.14/1.38      inference('cnf', [status(esa)], [cc1_relat_1])).
% 1.14/1.38  thf(d7_relat_1, axiom,
% 1.14/1.38    (![A:$i]:
% 1.14/1.38     ( ( v1_relat_1 @ A ) =>
% 1.14/1.38       ( ![B:$i]:
% 1.14/1.38         ( ( v1_relat_1 @ B ) =>
% 1.14/1.38           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 1.14/1.38             ( ![C:$i,D:$i]:
% 1.14/1.38               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 1.14/1.38                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 1.14/1.38  thf('14', plain,
% 1.14/1.38      (![X18 : $i, X19 : $i]:
% 1.14/1.38         (~ (v1_relat_1 @ X18)
% 1.14/1.38          | (r2_hidden @ 
% 1.14/1.38             (k4_tarski @ (sk_C_2 @ X18 @ X19) @ (sk_D_3 @ X18 @ X19)) @ X18)
% 1.14/1.38          | (r2_hidden @ 
% 1.14/1.38             (k4_tarski @ (sk_D_3 @ X18 @ X19) @ (sk_C_2 @ X18 @ X19)) @ X19)
% 1.14/1.38          | ((X18) = (k4_relat_1 @ X19))
% 1.14/1.38          | ~ (v1_relat_1 @ X19))),
% 1.14/1.38      inference('cnf', [status(esa)], [d7_relat_1])).
% 1.14/1.38  thf(t7_tarski, axiom,
% 1.14/1.38    (![A:$i,B:$i]:
% 1.14/1.38     ( ~( ( r2_hidden @ A @ B ) & 
% 1.14/1.38          ( ![C:$i]:
% 1.14/1.38            ( ~( ( r2_hidden @ C @ B ) & 
% 1.14/1.38                 ( ![D:$i]:
% 1.14/1.38                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 1.14/1.38  thf('15', plain,
% 1.14/1.38      (![X7 : $i, X8 : $i]:
% 1.14/1.38         (~ (r2_hidden @ X7 @ X8) | (r2_hidden @ (sk_C @ X8) @ X8))),
% 1.14/1.38      inference('cnf', [status(esa)], [t7_tarski])).
% 1.14/1.38  thf('16', plain,
% 1.14/1.38      (![X0 : $i, X1 : $i]:
% 1.14/1.38         (~ (v1_relat_1 @ X1)
% 1.14/1.38          | ((X0) = (k4_relat_1 @ X1))
% 1.14/1.38          | (r2_hidden @ 
% 1.14/1.38             (k4_tarski @ (sk_D_3 @ X0 @ X1) @ (sk_C_2 @ X0 @ X1)) @ X1)
% 1.14/1.38          | ~ (v1_relat_1 @ X0)
% 1.14/1.38          | (r2_hidden @ (sk_C @ X0) @ X0))),
% 1.14/1.38      inference('sup-', [status(thm)], ['14', '15'])).
% 1.14/1.38  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.14/1.38      inference('condensation', [status(thm)], ['4'])).
% 1.14/1.38  thf('18', plain,
% 1.14/1.38      (![X0 : $i]:
% 1.14/1.38         ((r2_hidden @ (sk_C @ X0) @ X0)
% 1.14/1.38          | ~ (v1_relat_1 @ X0)
% 1.14/1.38          | ((X0) = (k4_relat_1 @ k1_xboole_0))
% 1.14/1.38          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.14/1.38      inference('sup-', [status(thm)], ['16', '17'])).
% 1.14/1.38  thf('19', plain,
% 1.14/1.38      (![X0 : $i]:
% 1.14/1.38         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.14/1.38          | ((X0) = (k4_relat_1 @ k1_xboole_0))
% 1.14/1.38          | ~ (v1_relat_1 @ X0)
% 1.14/1.38          | (r2_hidden @ (sk_C @ X0) @ X0))),
% 1.14/1.38      inference('sup-', [status(thm)], ['13', '18'])).
% 1.14/1.38  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.14/1.38  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.14/1.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.14/1.38  thf('21', plain,
% 1.14/1.38      (![X0 : $i]:
% 1.14/1.38         (((X0) = (k4_relat_1 @ k1_xboole_0))
% 1.14/1.38          | ~ (v1_relat_1 @ X0)
% 1.14/1.38          | (r2_hidden @ (sk_C @ X0) @ X0))),
% 1.14/1.38      inference('demod', [status(thm)], ['19', '20'])).
% 1.14/1.38  thf('22', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.14/1.38      inference('clc', [status(thm)], ['9', '10'])).
% 1.14/1.38  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.14/1.38      inference('condensation', [status(thm)], ['4'])).
% 1.14/1.38  thf('24', plain,
% 1.14/1.38      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 1.14/1.38      inference('sup-', [status(thm)], ['22', '23'])).
% 1.14/1.38  thf('25', plain,
% 1.14/1.38      (![X0 : $i]:
% 1.14/1.38         (~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X0))
% 1.14/1.38          | ((k4_xboole_0 @ X0 @ X0) = (k4_relat_1 @ k1_xboole_0)))),
% 1.14/1.38      inference('sup-', [status(thm)], ['21', '24'])).
% 1.14/1.38  thf('26', plain,
% 1.14/1.38      (![X0 : $i]:
% 1.14/1.38         (~ (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))
% 1.14/1.38          | ((k4_xboole_0 @ X0 @ X0) = (k4_relat_1 @ k1_xboole_0)))),
% 1.14/1.38      inference('sup-', [status(thm)], ['12', '25'])).
% 1.14/1.38  thf('27', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.14/1.38      inference('clc', [status(thm)], ['9', '10'])).
% 1.14/1.38  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.14/1.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.14/1.38  thf('29', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 1.14/1.38      inference('sup+', [status(thm)], ['27', '28'])).
% 1.14/1.38  thf('30', plain,
% 1.14/1.38      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_relat_1 @ k1_xboole_0))),
% 1.14/1.38      inference('demod', [status(thm)], ['26', '29'])).
% 1.14/1.38  thf('31', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.14/1.38      inference('sup+', [status(thm)], ['11', '30'])).
% 1.14/1.38  thf(t66_relat_1, conjecture,
% 1.14/1.38    (( k4_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 1.14/1.38  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.38    (( k4_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 1.14/1.38    inference('cnf.neg', [status(esa)], [t66_relat_1])).
% 1.14/1.38  thf('32', plain, (((k4_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 1.14/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.38  thf('33', plain, ($false),
% 1.14/1.38      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 1.14/1.38  
% 1.14/1.38  % SZS output end Refutation
% 1.14/1.38  
% 1.14/1.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
