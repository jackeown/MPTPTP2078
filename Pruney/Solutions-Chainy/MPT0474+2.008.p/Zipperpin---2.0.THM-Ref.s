%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9pWAhbod4j

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:55 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   32 (  53 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  177 ( 343 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('0',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X35 @ X36 ) @ ( sk_D_2 @ X35 @ X36 ) ) @ X35 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X35 @ X36 ) @ ( sk_C_2 @ X35 @ X36 ) ) @ X36 )
      | ( X35
        = ( k4_relat_1 @ X36 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
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
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ k1_xboole_0 @ X0 ) @ ( sk_C_2 @ k1_xboole_0 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('7',plain,(
    ! [X32: $i] :
      ( ( v1_relat_1 @ X32 )
      | ( r2_hidden @ ( sk_B @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('9',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ k1_xboole_0 @ X0 ) @ ( sk_C_2 @ k1_xboole_0 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['4'])).

thf('12',plain,
    ( ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('14',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t66_relat_1,conjecture,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t66_relat_1])).

thf('15',plain,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9pWAhbod4j
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.18/1.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.18/1.38  % Solved by: fo/fo7.sh
% 1.18/1.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.38  % done 1132 iterations in 0.921s
% 1.18/1.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.18/1.38  % SZS output start Refutation
% 1.18/1.38  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.18/1.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.18/1.38  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.18/1.38  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.18/1.38  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 1.18/1.38  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.18/1.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.18/1.38  thf(sk_B_type, type, sk_B: $i > $i).
% 1.18/1.38  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.18/1.38  thf(d7_relat_1, axiom,
% 1.18/1.38    (![A:$i]:
% 1.18/1.38     ( ( v1_relat_1 @ A ) =>
% 1.18/1.38       ( ![B:$i]:
% 1.18/1.38         ( ( v1_relat_1 @ B ) =>
% 1.18/1.38           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 1.18/1.38             ( ![C:$i,D:$i]:
% 1.18/1.38               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 1.18/1.38                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 1.18/1.38  thf('0', plain,
% 1.18/1.38      (![X35 : $i, X36 : $i]:
% 1.18/1.38         (~ (v1_relat_1 @ X35)
% 1.18/1.38          | (r2_hidden @ 
% 1.18/1.38             (k4_tarski @ (sk_C_2 @ X35 @ X36) @ (sk_D_2 @ X35 @ X36)) @ X35)
% 1.18/1.38          | (r2_hidden @ 
% 1.18/1.38             (k4_tarski @ (sk_D_2 @ X35 @ X36) @ (sk_C_2 @ X35 @ X36)) @ X36)
% 1.18/1.38          | ((X35) = (k4_relat_1 @ X36))
% 1.18/1.38          | ~ (v1_relat_1 @ X36))),
% 1.18/1.38      inference('cnf', [status(esa)], [d7_relat_1])).
% 1.18/1.38  thf(t4_boole, axiom,
% 1.18/1.38    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.18/1.38  thf('1', plain,
% 1.18/1.38      (![X13 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 1.18/1.38      inference('cnf', [status(esa)], [t4_boole])).
% 1.18/1.38  thf(d5_xboole_0, axiom,
% 1.18/1.38    (![A:$i,B:$i,C:$i]:
% 1.18/1.38     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.18/1.38       ( ![D:$i]:
% 1.18/1.38         ( ( r2_hidden @ D @ C ) <=>
% 1.18/1.38           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.18/1.38  thf('2', plain,
% 1.18/1.38      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.18/1.38         (~ (r2_hidden @ X6 @ X5)
% 1.18/1.38          | ~ (r2_hidden @ X6 @ X4)
% 1.18/1.38          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.18/1.38      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.18/1.38  thf('3', plain,
% 1.18/1.38      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.18/1.38         (~ (r2_hidden @ X6 @ X4)
% 1.18/1.38          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.18/1.38      inference('simplify', [status(thm)], ['2'])).
% 1.18/1.38  thf('4', plain,
% 1.18/1.38      (![X0 : $i, X1 : $i]:
% 1.18/1.38         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['1', '3'])).
% 1.18/1.38  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.18/1.38      inference('condensation', [status(thm)], ['4'])).
% 1.18/1.38  thf('6', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         (~ (v1_relat_1 @ X0)
% 1.18/1.38          | ((k1_xboole_0) = (k4_relat_1 @ X0))
% 1.18/1.38          | (r2_hidden @ 
% 1.18/1.38             (k4_tarski @ (sk_D_2 @ k1_xboole_0 @ X0) @ 
% 1.18/1.38              (sk_C_2 @ k1_xboole_0 @ X0)) @ 
% 1.18/1.38             X0)
% 1.18/1.38          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['0', '5'])).
% 1.18/1.38  thf(d1_relat_1, axiom,
% 1.18/1.38    (![A:$i]:
% 1.18/1.38     ( ( v1_relat_1 @ A ) <=>
% 1.18/1.38       ( ![B:$i]:
% 1.18/1.38         ( ~( ( r2_hidden @ B @ A ) & 
% 1.18/1.38              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 1.18/1.38  thf('7', plain,
% 1.18/1.38      (![X32 : $i]: ((v1_relat_1 @ X32) | (r2_hidden @ (sk_B @ X32) @ X32))),
% 1.18/1.38      inference('cnf', [status(esa)], [d1_relat_1])).
% 1.18/1.38  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.18/1.38      inference('condensation', [status(thm)], ['4'])).
% 1.18/1.38  thf('9', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.18/1.38      inference('sup-', [status(thm)], ['7', '8'])).
% 1.18/1.38  thf('10', plain,
% 1.18/1.38      (![X0 : $i]:
% 1.18/1.38         (~ (v1_relat_1 @ X0)
% 1.18/1.38          | ((k1_xboole_0) = (k4_relat_1 @ X0))
% 1.18/1.38          | (r2_hidden @ 
% 1.18/1.38             (k4_tarski @ (sk_D_2 @ k1_xboole_0 @ X0) @ 
% 1.18/1.38              (sk_C_2 @ k1_xboole_0 @ X0)) @ 
% 1.18/1.38             X0))),
% 1.18/1.38      inference('demod', [status(thm)], ['6', '9'])).
% 1.18/1.38  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.18/1.38      inference('condensation', [status(thm)], ['4'])).
% 1.18/1.38  thf('12', plain,
% 1.18/1.38      ((((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 1.18/1.38        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.18/1.38      inference('sup-', [status(thm)], ['10', '11'])).
% 1.18/1.38  thf('13', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.18/1.38      inference('sup-', [status(thm)], ['7', '8'])).
% 1.18/1.38  thf('14', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.18/1.38      inference('demod', [status(thm)], ['12', '13'])).
% 1.18/1.38  thf(t66_relat_1, conjecture,
% 1.18/1.38    (( k4_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 1.18/1.38  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.38    (( k4_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 1.18/1.38    inference('cnf.neg', [status(esa)], [t66_relat_1])).
% 1.18/1.38  thf('15', plain, (((k4_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 1.18/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.38  thf('16', plain, ($false),
% 1.18/1.38      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 1.18/1.38  
% 1.18/1.38  % SZS output end Refutation
% 1.18/1.38  
% 1.18/1.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
