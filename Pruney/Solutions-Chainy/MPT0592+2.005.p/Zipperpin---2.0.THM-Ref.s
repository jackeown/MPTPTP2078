%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gAs2S5srcl

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  33 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  114 ( 247 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t196_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( ( ( k1_relat_1 @ A )
                = k1_xboole_0 )
              & ( ( k1_relat_1 @ B )
                = k1_xboole_0 ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( ( ( k1_relat_1 @ A )
                  = k1_xboole_0 )
                & ( ( k1_relat_1 @ B )
                  = k1_xboole_0 ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t196_relat_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( k1_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('8',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    sk_B = sk_A ),
    inference('sup+',[status(thm)],['5','11'])).

thf('13',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gAs2S5srcl
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:25:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 7 iterations in 0.008s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(t196_relat_1, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ A ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( v1_relat_1 @ B ) =>
% 0.21/0.46           ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.46               ( ( k1_relat_1 @ B ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.46             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( v1_relat_1 @ A ) =>
% 0.21/0.46          ( ![B:$i]:
% 0.21/0.46            ( ( v1_relat_1 @ B ) =>
% 0.21/0.46              ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.46                  ( ( k1_relat_1 @ B ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.46                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t196_relat_1])).
% 0.21/0.46  thf('0', plain, (((k1_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t64_relat_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ A ) =>
% 0.21/0.46       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.46           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.46         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.46          | ((X0) = (k1_xboole_0))
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.46        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.46        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.46  thf('5', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.46  thf('6', plain, (((k1_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.46          | ((X0) = (k1_xboole_0))
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.46        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.46        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('11', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.46  thf('12', plain, (((sk_B) = (sk_A))),
% 0.21/0.46      inference('sup+', [status(thm)], ['5', '11'])).
% 0.21/0.46  thf('13', plain, (((sk_A) != (sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('14', plain, ($false),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
