%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.730j2klzTs

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  58 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  392 ( 830 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(t42_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) )
          & ! [D: $i] :
              ( ( r2_hidden @ D @ ( k1_wellord1 @ C @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ D @ B ) @ C )
                & ( D != B ) ) ) )
       => ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( ( v2_wellord1 @ C )
            & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) )
            & ! [D: $i] :
                ( ( r2_hidden @ D @ ( k1_wellord1 @ C @ A ) )
               => ( ( r2_hidden @ ( k4_tarski @ D @ B ) @ C )
                  & ( D != B ) ) ) )
         => ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_wellord1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X13 @ sk_B ) @ sk_C_1 )
      | ~ ( r2_hidden @ X13 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( X7
       != ( k1_wellord1 @ X6 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X5 ) @ X6 )
      | ( X9 = X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( X9 = X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X5 ) @ X6 )
      | ( r2_hidden @ X9 @ ( k1_wellord1 @ X6 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
        = sk_B )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
      | ( ( sk_C @ X0 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,
    ( ( ( sk_C @ ( k1_wellord1 @ sk_C_1 @ sk_B ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
      = sk_B )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
    | ( ( sk_C @ ( k1_wellord1 @ sk_C_1 @ sk_B ) @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
      = sk_B ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,
    ( ( r2_hidden @ sk_B @ ( k1_wellord1 @ sk_C_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X13: $i] :
      ( ( X13 != sk_B )
      | ~ ( r2_hidden @ X13 @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_wellord1 @ sk_C_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r1_tarski @ ( k1_wellord1 @ sk_C_1 @ sk_A ) @ ( k1_wellord1 @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['14','16'])).

thf(t37_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( v2_wellord1 @ C )
          & ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_wellord1 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ ( k1_wellord1 @ X10 @ X11 ) @ ( k1_wellord1 @ X10 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t37_wellord1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( v2_wellord1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_wellord1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.730j2klzTs
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:37:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 23 iterations in 0.019s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.48  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.21/0.48  thf(t42_wellord1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ C ) =>
% 0.21/0.48       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.48           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.48           ( ![D:$i]:
% 0.21/0.48             ( ( r2_hidden @ D @ ( k1_wellord1 @ C @ A ) ) =>
% 0.21/0.48               ( ( r2_hidden @ ( k4_tarski @ D @ B ) @ C ) & ( ( D ) != ( B ) ) ) ) ) ) =>
% 0.21/0.48         ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( v1_relat_1 @ C ) =>
% 0.21/0.48          ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.48              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.48              ( ![D:$i]:
% 0.21/0.48                ( ( r2_hidden @ D @ ( k1_wellord1 @ C @ A ) ) =>
% 0.21/0.48                  ( ( r2_hidden @ ( k4_tarski @ D @ B ) @ C ) & 
% 0.21/0.48                    ( ( D ) != ( B ) ) ) ) ) ) =>
% 0.21/0.48            ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t42_wellord1])).
% 0.21/0.48  thf('0', plain, (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d3_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X13 : $i]:
% 0.21/0.48         ((r2_hidden @ (k4_tarski @ X13 @ sk_B) @ sk_C_1)
% 0.21/0.48          | ~ (r2_hidden @ X13 @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.21/0.48          | (r2_hidden @ 
% 0.21/0.48             (k4_tarski @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ sk_B) @ 
% 0.21/0.48             sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf(d1_wellord1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i,C:$i]:
% 0.21/0.48         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.21/0.48           ( ![D:$i]:
% 0.21/0.48             ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.48               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.21/0.48         (((X7) != (k1_wellord1 @ X6 @ X5))
% 0.21/0.48          | (r2_hidden @ X9 @ X7)
% 0.21/0.48          | ~ (r2_hidden @ (k4_tarski @ X9 @ X5) @ X6)
% 0.21/0.48          | ((X9) = (X5))
% 0.21/0.48          | ~ (v1_relat_1 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X6)
% 0.21/0.48          | ((X9) = (X5))
% 0.21/0.48          | ~ (r2_hidden @ (k4_tarski @ X9 @ X5) @ X6)
% 0.21/0.48          | (r2_hidden @ X9 @ (k1_wellord1 @ X6 @ X5)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.21/0.48          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.21/0.48             (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.21/0.48          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) = (sk_B))
% 0.21/0.48          | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.48  thf('7', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ X0)
% 0.21/0.48          | (r2_hidden @ (sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) @ 
% 0.21/0.48             (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.21/0.48          | ((sk_C @ X0 @ (k1_wellord1 @ sk_C_1 @ sk_A)) = (sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((((sk_C @ (k1_wellord1 @ sk_C_1 @ sk_B) @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.21/0.48          = (sk_B))
% 0.21/0.48        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.21/0.48           (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.21/0.48        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.21/0.48           (k1_wellord1 @ sk_C_1 @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.21/0.48         (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.21/0.48        | ((sk_C @ (k1_wellord1 @ sk_C_1 @ sk_B) @ 
% 0.21/0.48            (k1_wellord1 @ sk_C_1 @ sk_A)) = (sk_B)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ (k1_wellord1 @ sk_C_1 @ sk_A))
% 0.21/0.48        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.21/0.48           (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.21/0.48        | (r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.21/0.48           (k1_wellord1 @ sk_C_1 @ sk_B)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.21/0.48         (k1_wellord1 @ sk_C_1 @ sk_B))
% 0.21/0.48        | (r2_hidden @ sk_B @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X13 : $i]:
% 0.21/0.48         (((X13) != (sk_B))
% 0.21/0.48          | ~ (r2_hidden @ X13 @ (k1_wellord1 @ sk_C_1 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain, (~ (r2_hidden @ sk_B @ (k1_wellord1 @ sk_C_1 @ sk_A))),
% 0.21/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((r1_tarski @ (k1_wellord1 @ sk_C_1 @ sk_A) @ 
% 0.21/0.48        (k1_wellord1 @ sk_C_1 @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['14', '16'])).
% 0.21/0.48  thf(t37_wellord1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ C ) =>
% 0.21/0.48       ( ( ( v2_wellord1 @ C ) & ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.48           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) =>
% 0.21/0.48         ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.48           ( r1_tarski @ ( k1_wellord1 @ C @ A ) @ ( k1_wellord1 @ C @ B ) ) ) ) ))).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (v2_wellord1 @ X10)
% 0.21/0.48          | ~ (r2_hidden @ X11 @ (k3_relat_1 @ X10))
% 0.21/0.48          | ~ (r2_hidden @ X12 @ (k3_relat_1 @ X10))
% 0.21/0.48          | ~ (r1_tarski @ (k1_wellord1 @ X10 @ X11) @ 
% 0.21/0.48               (k1_wellord1 @ X10 @ X12))
% 0.21/0.48          | (r2_hidden @ (k4_tarski @ X11 @ X12) @ X10)
% 0.21/0.48          | ~ (v1_relat_1 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [t37_wellord1])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_C_1)
% 0.21/0.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.21/0.48        | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))
% 0.21/0.48        | ~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))
% 0.21/0.48        | ~ (v2_wellord1 @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('22', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain, ((v2_wellord1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.21/0.48  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
