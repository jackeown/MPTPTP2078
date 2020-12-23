%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GjJSldfh1t

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  248 ( 419 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t163_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t163_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
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
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( r1_tarski @ X7 @ ( k10_relat_1 @ X8 @ ( k9_relat_1 @ X8 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( r1_tarski @ ( k10_relat_1 @ X6 @ X4 ) @ ( k10_relat_1 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GjJSldfh1t
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 28 iterations in 0.020s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(t163_funct_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.47           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.20/0.47         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.47              ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.20/0.47            ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t163_funct_1])).
% 0.20/0.47  thf('0', plain, (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C_1 @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d3_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X1 : $i, X3 : $i]:
% 0.20/0.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.47  thf('2', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t146_funct_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.47         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X7 @ (k1_relat_1 @ X8))
% 0.20/0.47          | (r1_tarski @ X7 @ (k10_relat_1 @ X8 @ (k9_relat_1 @ X8 @ X7)))
% 0.20/0.47          | ~ (v1_relat_1 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.47        | (r1_tarski @ sk_A @ 
% 0.20/0.47           (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((r1_tarski @ sk_A @ 
% 0.20/0.47        (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.47          | (r2_hidden @ X0 @ X2)
% 0.20/0.47          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ X0 @ 
% 0.20/0.47           (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A)))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ sk_A @ X0)
% 0.20/0.47          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 0.20/0.47             (k10_relat_1 @ sk_C_1 @ (k9_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '8'])).
% 0.20/0.47  thf('10', plain, ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t178_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ C ) =>
% 0.20/0.47       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.47         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X4 @ X5)
% 0.20/0.47          | ~ (v1_relat_1 @ X6)
% 0.20/0.47          | (r1_tarski @ (k10_relat_1 @ X6 @ X4) @ (k10_relat_1 @ X6 @ X5)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.20/0.47           (k10_relat_1 @ X0 @ sk_B))
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.47          | (r2_hidden @ X0 @ X2)
% 0.20/0.47          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | (r2_hidden @ X1 @ (k10_relat_1 @ X0 @ sk_B))
% 0.20/0.47          | ~ (r2_hidden @ X1 @ 
% 0.20/0.47               (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ sk_A @ X0)
% 0.20/0.47          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k10_relat_1 @ sk_C_1 @ sk_B))
% 0.20/0.47          | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '14'])).
% 0.20/0.47  thf('16', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ sk_A @ X0)
% 0.20/0.47          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k10_relat_1 @ sk_C_1 @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X1 : $i, X3 : $i]:
% 0.20/0.47         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C_1 @ sk_B))
% 0.20/0.47        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C_1 @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain, ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C_1 @ sk_B))),
% 0.20/0.47      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.47  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
