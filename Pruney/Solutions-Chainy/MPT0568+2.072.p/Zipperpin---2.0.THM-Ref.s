%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6VFeey2Er2

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:57 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  160 ( 197 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X45 @ ( k10_relat_1 @ X46 @ X44 ) )
      | ( r2_hidden @ ( k4_tarski @ X45 @ ( sk_D_1 @ X46 @ X44 @ X45 ) ) @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X1 @ X0 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 != X34 )
      | ~ ( r2_hidden @ X32 @ ( k4_xboole_0 @ X33 @ ( k1_tarski @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('6',plain,(
    ! [X33: $i,X34: $i] :
      ~ ( r2_hidden @ X34 @ ( k4_xboole_0 @ X33 @ ( k1_tarski @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('9',plain,(
    ! [X40: $i] :
      ( ( v1_relat_1 @ X40 )
      | ( r2_hidden @ ( sk_B_1 @ X40 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('11',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6VFeey2Er2
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 164 iterations in 0.157s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.61  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.39/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.39/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.61  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.39/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.61  thf(t172_relat_1, conjecture,
% 0.39/0.61    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.39/0.61  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(t7_xboole_0, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.39/0.61          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.39/0.61  thf('1', plain,
% 0.39/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.39/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.61  thf(t166_relat_1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ C ) =>
% 0.39/0.61       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.39/0.61         ( ?[D:$i]:
% 0.39/0.61           ( ( r2_hidden @ D @ B ) & 
% 0.39/0.61             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.39/0.61             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.39/0.61  thf('2', plain,
% 0.39/0.61      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X45 @ (k10_relat_1 @ X46 @ X44))
% 0.39/0.61          | (r2_hidden @ (k4_tarski @ X45 @ (sk_D_1 @ X46 @ X44 @ X45)) @ X46)
% 0.39/0.61          | ~ (v1_relat_1 @ X46))),
% 0.39/0.61      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.39/0.61  thf('3', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.39/0.61          | ~ (v1_relat_1 @ X1)
% 0.39/0.61          | (r2_hidden @ 
% 0.39/0.61             (k4_tarski @ (sk_B @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.39/0.61              (sk_D_1 @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0)))) @ 
% 0.39/0.61             X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.61  thf(t4_boole, axiom,
% 0.39/0.61    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.39/0.61  thf('4', plain,
% 0.39/0.61      (![X3 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.39/0.61      inference('cnf', [status(esa)], [t4_boole])).
% 0.39/0.61  thf(t64_zfmisc_1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.39/0.61       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.39/0.61  thf('5', plain,
% 0.39/0.61      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.61         (((X32) != (X34))
% 0.39/0.61          | ~ (r2_hidden @ X32 @ (k4_xboole_0 @ X33 @ (k1_tarski @ X34))))),
% 0.39/0.61      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (![X33 : $i, X34 : $i]:
% 0.39/0.61         ~ (r2_hidden @ X34 @ (k4_xboole_0 @ X33 @ (k1_tarski @ X34)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.61  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.61      inference('sup-', [status(thm)], ['4', '6'])).
% 0.39/0.61  thf('8', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ k1_xboole_0)
% 0.39/0.61          | ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['3', '7'])).
% 0.39/0.61  thf(d1_relat_1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ A ) <=>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ~( ( r2_hidden @ B @ A ) & 
% 0.39/0.61              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (![X40 : $i]: ((v1_relat_1 @ X40) | (r2_hidden @ (sk_B_1 @ X40) @ X40))),
% 0.39/0.61      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.39/0.61  thf('10', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.61      inference('sup-', [status(thm)], ['4', '6'])).
% 0.39/0.61  thf('11', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.61  thf('12', plain,
% 0.39/0.61      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['8', '11'])).
% 0.39/0.61  thf('13', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['0', '12'])).
% 0.39/0.61  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.39/0.61  
% 0.39/0.61  % SZS output end Refutation
% 0.39/0.61  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
