%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.edZ1iElJrS

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    3
%              Number of atoms          :   53 (  53 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X6: $i] :
      ( ( X6
       != ( k1_setfam_1 @ X1 ) )
      | ( X6 = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('1',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['0'])).

thf(t2_setfam_1,conjecture,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k1_setfam_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t2_setfam_1])).

thf('2',plain,(
    ( k1_setfam_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['1','2'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.edZ1iElJrS
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 15:48:00 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.19/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.44  % Solved by: fo/fo7.sh
% 0.19/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.44  % done 1 iterations in 0.006s
% 0.19/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.44  % SZS output start Refutation
% 0.19/0.44  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.44  thf(d1_setfam_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.19/0.44         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.44       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.19/0.44         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.19/0.44           ( ![C:$i]:
% 0.19/0.44             ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.44               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.19/0.44  thf('0', plain,
% 0.19/0.44      (![X1 : $i, X6 : $i]:
% 0.19/0.44         (((X6) != (k1_setfam_1 @ X1))
% 0.19/0.44          | ((X6) = (k1_xboole_0))
% 0.19/0.44          | ((X1) != (k1_xboole_0)))),
% 0.19/0.44      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.19/0.44  thf('1', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.44      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.44  thf(t2_setfam_1, conjecture,
% 0.19/0.44    (( k1_setfam_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.19/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.44    (( k1_setfam_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.19/0.44    inference('cnf.neg', [status(esa)], [t2_setfam_1])).
% 0.19/0.44  thf('2', plain, (((k1_setfam_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('3', plain, ($false),
% 0.19/0.44      inference('simplify_reflect-', [status(thm)], ['1', '2'])).
% 0.19/0.44  
% 0.19/0.44  % SZS output end Refutation
% 0.19/0.44  
% 0.19/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
