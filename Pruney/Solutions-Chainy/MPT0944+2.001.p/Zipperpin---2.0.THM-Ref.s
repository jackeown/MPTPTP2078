%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gADGzBKbPk

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 ( 136 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X3 ) )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t9_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ B @ A )
         => ( v2_wellord1 @ ( k1_wellord2 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( r1_tarski @ B @ A )
           => ( v2_wellord1 @ ( k1_wellord2 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_wellord2])).

thf('1',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X5 ) @ X4 )
        = ( k1_wellord2 @ X4 ) )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('3',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B )
    = ( k1_wellord2 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t32_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( v2_wellord1 @ ( k2_wellord1 @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v2_wellord1 @ ( k2_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t32_wellord1])).

thf('5',plain,
    ( ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('7',plain,
    ( ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gADGzBKbPk
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:18:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 9 iterations in 0.007s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.45  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.20/0.45  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.45  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(t7_wellord2, axiom,
% 0.20/0.45    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X3 : $i]: ((v2_wellord1 @ (k1_wellord2 @ X3)) | ~ (v3_ordinal1 @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.20/0.45  thf(t9_wellord2, conjecture,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( r1_tarski @ B @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ B ) ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i]:
% 0.20/0.45        ( ( v3_ordinal1 @ A ) =>
% 0.20/0.45          ( ![B:$i]:
% 0.20/0.45            ( ( r1_tarski @ B @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ B ) ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t9_wellord2])).
% 0.20/0.45  thf('1', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t8_wellord2, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.45       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X4 : $i, X5 : $i]:
% 0.20/0.45         (((k2_wellord1 @ (k1_wellord2 @ X5) @ X4) = (k1_wellord2 @ X4))
% 0.20/0.45          | ~ (r1_tarski @ X4 @ X5))),
% 0.20/0.45      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (((k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B) = (k1_wellord2 @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.45  thf(t32_wellord1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ( v2_wellord1 @ B ) => ( v2_wellord1 @ ( k2_wellord1 @ B @ A ) ) ) ))).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (~ (v2_wellord1 @ X0)
% 0.20/0.45          | (v2_wellord1 @ (k2_wellord1 @ X0 @ X1))
% 0.20/0.45          | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t32_wellord1])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (((v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.20/0.45        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.20/0.45        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A)))),
% 0.20/0.45      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.45  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.45  thf('6', plain, (![X2 : $i]: (v1_relat_1 @ (k1_wellord2 @ X2))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (((v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.20/0.45        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A)))),
% 0.20/0.45      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.45  thf('8', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_B))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('9', plain, (~ (v2_wellord1 @ (k1_wellord2 @ sk_A))),
% 0.20/0.45      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.45  thf('10', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '9'])).
% 0.20/0.45  thf('11', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('12', plain, ($false), inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
