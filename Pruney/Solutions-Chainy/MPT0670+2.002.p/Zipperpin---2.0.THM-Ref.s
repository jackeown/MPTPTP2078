%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rXXNrM1tOg

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  59 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  324 ( 608 expanded)
%              Number of equality atoms :    8 (  23 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(fc9_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf(t87_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
       => ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
         => ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_1])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( X12
       != ( k1_funct_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ ( k1_funct_1 @ X11 @ X10 ) ) @ X11 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X6 @ X7 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) @ sk_A ) ) @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) @ sk_A ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ X11 )
      | ( X12
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) @ sk_A )
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) @ sk_A )
    = ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C_1 ) @ sk_A )
 != ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rXXNrM1tOg
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:35:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 25 iterations in 0.021s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.44  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.44  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.44  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.44  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(dt_k8_relat_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.20/0.44  thf('0', plain,
% 0.20/0.44      (![X4 : $i, X5 : $i]:
% 0.20/0.44         ((v1_relat_1 @ (k8_relat_1 @ X4 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.20/0.44      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.20/0.44  thf(fc9_funct_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.44       ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) & 
% 0.20/0.44         ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ))).
% 0.20/0.44  thf('1', plain,
% 0.20/0.44      (![X8 : $i, X9 : $i]:
% 0.20/0.44         ((v1_funct_1 @ (k8_relat_1 @ X8 @ X9))
% 0.20/0.44          | ~ (v1_funct_1 @ X9)
% 0.20/0.44          | ~ (v1_relat_1 @ X9))),
% 0.20/0.44      inference('cnf', [status(esa)], [fc9_funct_1])).
% 0.20/0.44  thf(t87_funct_1, conjecture,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.44       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) =>
% 0.20/0.44         ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.44        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.44          ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) =>
% 0.20/0.44            ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A ) =
% 0.20/0.44              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t87_funct_1])).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(t8_funct_1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.44       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.44         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.44           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.44  thf('3', plain,
% 0.20/0.44      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.44         (~ (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.20/0.44          | ((X12) != (k1_funct_1 @ X11 @ X10))
% 0.20/0.44          | (r2_hidden @ (k4_tarski @ X10 @ X12) @ X11)
% 0.20/0.44          | ~ (v1_funct_1 @ X11)
% 0.20/0.44          | ~ (v1_relat_1 @ X11))),
% 0.20/0.44      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.44  thf('4', plain,
% 0.20/0.44      (![X10 : $i, X11 : $i]:
% 0.20/0.44         (~ (v1_relat_1 @ X11)
% 0.20/0.44          | ~ (v1_funct_1 @ X11)
% 0.20/0.44          | (r2_hidden @ (k4_tarski @ X10 @ (k1_funct_1 @ X11 @ X10)) @ X11)
% 0.20/0.44          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X11)))),
% 0.20/0.44      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      (((r2_hidden @ 
% 0.20/0.44         (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C_1) @ sk_A)) @ 
% 0.20/0.44         (k8_relat_1 @ sk_B @ sk_C_1))
% 0.20/0.44        | ~ (v1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C_1))
% 0.20/0.44        | ~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      ((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.44        | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.44        | ~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1))
% 0.20/0.44        | (r2_hidden @ 
% 0.20/0.44           (k4_tarski @ sk_A @ 
% 0.20/0.44            (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C_1) @ sk_A)) @ 
% 0.20/0.44           (k8_relat_1 @ sk_B @ sk_C_1)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['1', '5'])).
% 0.20/0.44  thf('7', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      ((~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C_1))
% 0.20/0.44        | (r2_hidden @ 
% 0.20/0.44           (k4_tarski @ sk_A @ 
% 0.20/0.44            (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C_1) @ sk_A)) @ 
% 0.20/0.44           (k8_relat_1 @ sk_B @ sk_C_1)))),
% 0.20/0.44      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.44  thf('10', plain,
% 0.20/0.44      ((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.44        | (r2_hidden @ 
% 0.20/0.44           (k4_tarski @ sk_A @ 
% 0.20/0.44            (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C_1) @ sk_A)) @ 
% 0.20/0.44           (k8_relat_1 @ sk_B @ sk_C_1)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['0', '9'])).
% 0.20/0.44  thf('11', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('12', plain,
% 0.20/0.44      ((r2_hidden @ 
% 0.20/0.44        (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C_1) @ sk_A)) @ 
% 0.20/0.44        (k8_relat_1 @ sk_B @ sk_C_1))),
% 0.20/0.44      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.44  thf(t117_relat_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.20/0.44  thf('13', plain,
% 0.20/0.44      (![X6 : $i, X7 : $i]:
% 0.20/0.44         ((r1_tarski @ (k8_relat_1 @ X6 @ X7) @ X7) | ~ (v1_relat_1 @ X7))),
% 0.20/0.44      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.20/0.44  thf(d3_tarski, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.44       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.44  thf('14', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.44          | (r2_hidden @ X0 @ X2)
% 0.20/0.44          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.44  thf('15', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         (~ (v1_relat_1 @ X0)
% 0.20/0.44          | (r2_hidden @ X2 @ X0)
% 0.20/0.44          | ~ (r2_hidden @ X2 @ (k8_relat_1 @ X1 @ X0)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.44  thf('16', plain,
% 0.20/0.44      (((r2_hidden @ 
% 0.20/0.44         (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C_1) @ sk_A)) @ 
% 0.20/0.44         sk_C_1)
% 0.20/0.44        | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.44      inference('sup-', [status(thm)], ['12', '15'])).
% 0.20/0.44  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('18', plain,
% 0.20/0.44      ((r2_hidden @ 
% 0.20/0.44        (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C_1) @ sk_A)) @ 
% 0.20/0.44        sk_C_1)),
% 0.20/0.44      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.45  thf('19', plain,
% 0.20/0.45      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.45         (~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ X11)
% 0.20/0.45          | ((X12) = (k1_funct_1 @ X11 @ X10))
% 0.20/0.45          | ~ (v1_funct_1 @ X11)
% 0.20/0.45          | ~ (v1_relat_1 @ X11))),
% 0.20/0.45      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.45  thf('20', plain,
% 0.20/0.45      ((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.45        | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.45        | ((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C_1) @ sk_A)
% 0.20/0.45            = (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.45  thf('21', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('22', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('23', plain,
% 0.20/0.45      (((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C_1) @ sk_A)
% 0.20/0.45         = (k1_funct_1 @ sk_C_1 @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.45  thf('24', plain,
% 0.20/0.45      (((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C_1) @ sk_A)
% 0.20/0.45         != (k1_funct_1 @ sk_C_1 @ sk_A))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('25', plain, ($false),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
