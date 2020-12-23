%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kCKFMC5gBl

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:00 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   36 (  59 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  170 ( 329 expanded)
%              Number of equality atoms :   20 (  43 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d10_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
          <=> ( ( r2_hidden @ C @ A )
              & ( C = D ) ) ) ) ) )).

thf('0',plain,(
    ! [X90: $i,X91: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X90 @ X91 ) @ ( sk_D_2 @ X90 @ X91 ) ) @ X90 )
      | ( r2_hidden @ ( sk_C_2 @ X90 @ X91 ) @ X91 )
      | ( X90
        = ( k6_relat_1 @ X91 ) )
      | ~ ( v1_relat_1 @ X90 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X84: $i,X85: $i] :
      ( ( k6_subset_1 @ X84 @ X85 )
      = ( k4_xboole_0 @ X84 @ X85 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X16: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_hidden @ X75 @ X76 )
      | ( ( k4_xboole_0 @ X76 @ ( k1_tarski @ X75 ) )
       != X76 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('5',plain,(
    ! [X84: $i,X85: $i] :
      ( ( k6_subset_1 @ X84 @ X85 )
      = ( k4_xboole_0 @ X84 @ X85 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_hidden @ X75 @ X76 )
      | ( ( k6_subset_1 @ X76 @ ( k1_tarski @ X75 ) )
       != X76 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('10',plain,(
    ! [X97: $i] :
      ( ( v1_relat_1 @ X97 )
      | ( r2_hidden @ ( sk_B_2 @ X97 ) @ X97 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('12',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('15',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t81_relat_1,conjecture,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k6_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t81_relat_1])).

thf('16',plain,(
    ( k6_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kCKFMC5gBl
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:18:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.90/1.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.11  % Solved by: fo/fo7.sh
% 0.90/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.11  % done 1954 iterations in 0.654s
% 0.90/1.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.11  % SZS output start Refutation
% 0.90/1.11  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.11  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.90/1.11  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.90/1.11  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.90/1.11  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.90/1.11  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.11  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.11  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.90/1.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.11  thf(d10_relat_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( v1_relat_1 @ B ) =>
% 0.90/1.11       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.90/1.11         ( ![C:$i,D:$i]:
% 0.90/1.11           ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.90/1.11             ( ( r2_hidden @ C @ A ) & ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.90/1.11  thf('0', plain,
% 0.90/1.11      (![X90 : $i, X91 : $i]:
% 0.90/1.11         ((r2_hidden @ 
% 0.90/1.11           (k4_tarski @ (sk_C_2 @ X90 @ X91) @ (sk_D_2 @ X90 @ X91)) @ X90)
% 0.90/1.11          | (r2_hidden @ (sk_C_2 @ X90 @ X91) @ X91)
% 0.90/1.11          | ((X90) = (k6_relat_1 @ X91))
% 0.90/1.11          | ~ (v1_relat_1 @ X90))),
% 0.90/1.11      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.90/1.11  thf(t4_boole, axiom,
% 0.90/1.11    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.90/1.11  thf('1', plain,
% 0.90/1.11      (![X16 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.90/1.11      inference('cnf', [status(esa)], [t4_boole])).
% 0.90/1.11  thf(redefinition_k6_subset_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.90/1.11  thf('2', plain,
% 0.90/1.11      (![X84 : $i, X85 : $i]:
% 0.90/1.11         ((k6_subset_1 @ X84 @ X85) = (k4_xboole_0 @ X84 @ X85))),
% 0.90/1.11      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.90/1.11  thf('3', plain,
% 0.90/1.11      (![X16 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.90/1.11      inference('demod', [status(thm)], ['1', '2'])).
% 0.90/1.11  thf(t65_zfmisc_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.90/1.11       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.90/1.11  thf('4', plain,
% 0.90/1.11      (![X75 : $i, X76 : $i]:
% 0.90/1.11         (~ (r2_hidden @ X75 @ X76)
% 0.90/1.11          | ((k4_xboole_0 @ X76 @ (k1_tarski @ X75)) != (X76)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.90/1.11  thf('5', plain,
% 0.90/1.11      (![X84 : $i, X85 : $i]:
% 0.90/1.11         ((k6_subset_1 @ X84 @ X85) = (k4_xboole_0 @ X84 @ X85))),
% 0.90/1.11      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.90/1.11  thf('6', plain,
% 0.90/1.11      (![X75 : $i, X76 : $i]:
% 0.90/1.11         (~ (r2_hidden @ X75 @ X76)
% 0.90/1.11          | ((k6_subset_1 @ X76 @ (k1_tarski @ X75)) != (X76)))),
% 0.90/1.11      inference('demod', [status(thm)], ['4', '5'])).
% 0.90/1.11  thf('7', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['3', '6'])).
% 0.90/1.11  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.11      inference('simplify', [status(thm)], ['7'])).
% 0.90/1.11  thf('9', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (v1_relat_1 @ k1_xboole_0)
% 0.90/1.11          | ((k1_xboole_0) = (k6_relat_1 @ X0))
% 0.90/1.11          | (r2_hidden @ (sk_C_2 @ k1_xboole_0 @ X0) @ X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['0', '8'])).
% 0.90/1.11  thf(d1_relat_1, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( v1_relat_1 @ A ) <=>
% 0.90/1.11       ( ![B:$i]:
% 0.90/1.11         ( ~( ( r2_hidden @ B @ A ) & 
% 0.90/1.11              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.90/1.11  thf('10', plain,
% 0.90/1.11      (![X97 : $i]: ((v1_relat_1 @ X97) | (r2_hidden @ (sk_B_2 @ X97) @ X97))),
% 0.90/1.11      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.90/1.11  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.11      inference('simplify', [status(thm)], ['7'])).
% 0.90/1.11  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.90/1.11      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.11  thf('13', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (((k1_xboole_0) = (k6_relat_1 @ X0))
% 0.90/1.11          | (r2_hidden @ (sk_C_2 @ k1_xboole_0 @ X0) @ X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['9', '12'])).
% 0.90/1.11  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.11      inference('simplify', [status(thm)], ['7'])).
% 0.90/1.11  thf('15', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.11  thf(t81_relat_1, conjecture,
% 0.90/1.11    (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.90/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.11    (( k6_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.90/1.11    inference('cnf.neg', [status(esa)], [t81_relat_1])).
% 0.90/1.11  thf('16', plain, (((k6_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('17', plain, ($false),
% 0.90/1.11      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.90/1.11  
% 0.90/1.11  % SZS output end Refutation
% 0.90/1.11  
% 0.90/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
