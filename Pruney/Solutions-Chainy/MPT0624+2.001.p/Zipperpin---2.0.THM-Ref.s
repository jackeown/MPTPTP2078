%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yoBH83vEfI

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:46 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  44 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  237 ( 415 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_2_type,type,(
    sk_D_2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t19_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                    & ( C
                      = ( k1_funct_1 @ B @ D ) ) ) )
       => ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ! [D: $i] :
                    ~ ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                      & ( C
                        = ( k1_funct_1 @ B @ D ) ) ) )
         => ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
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
    ! [X11: $i] :
      ( ~ ( r2_hidden @ X11 @ sk_A )
      | ( X11
        = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X11: $i] :
      ( ~ ( r2_hidden @ X11 @ sk_A )
      | ( r2_hidden @ ( sk_D_2 @ X11 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_C @ X0 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X7: $i,X9: $i,X10: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X5 ) )
      | ( X9
       != ( k1_funct_1 @ X5 @ X10 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('8',plain,(
    ! [X5: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X5 @ X10 ) @ ( k2_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_A ) ) ) @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D_2 @ ( sk_C @ X0 @ sk_A ) ) ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,
    ( ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yoBH83vEfI
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 21 iterations in 0.019s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(sk_D_2_type, type, sk_D_2: $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.46  thf(t19_funct_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.46       ( ( ![C:$i]:
% 0.19/0.46           ( ~( ( r2_hidden @ C @ A ) & 
% 0.19/0.46                ( ![D:$i]:
% 0.19/0.46                  ( ~( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) & 
% 0.19/0.46                       ( ( C ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) =>
% 0.19/0.46         ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i]:
% 0.19/0.46        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.46          ( ( ![C:$i]:
% 0.19/0.46              ( ~( ( r2_hidden @ C @ A ) & 
% 0.19/0.46                   ( ![D:$i]:
% 0.19/0.46                     ( ~( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) & 
% 0.19/0.46                          ( ( C ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) =>
% 0.19/0.46            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t19_funct_1])).
% 0.19/0.46  thf('0', plain, (~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(d3_tarski, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X1 : $i, X3 : $i]:
% 0.19/0.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X11 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X11 @ sk_A)
% 0.19/0.46          | ((X11) = (k1_funct_1 @ sk_B @ (sk_D_2 @ X11))))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((r1_tarski @ sk_A @ X0)
% 0.19/0.46          | ((sk_C @ X0 @ sk_A)
% 0.19/0.46              = (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_A)))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X1 : $i, X3 : $i]:
% 0.19/0.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X11 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X11 @ sk_A)
% 0.19/0.46          | (r2_hidden @ (sk_D_2 @ X11) @ (k1_relat_1 @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((r1_tarski @ sk_A @ X0)
% 0.19/0.46          | (r2_hidden @ (sk_D_2 @ (sk_C @ X0 @ sk_A)) @ (k1_relat_1 @ sk_B)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.46  thf(d5_funct_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.19/0.46           ( ![C:$i]:
% 0.19/0.46             ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.46               ( ?[D:$i]:
% 0.19/0.46                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.19/0.46                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X5 : $i, X7 : $i, X9 : $i, X10 : $i]:
% 0.19/0.46         (((X7) != (k2_relat_1 @ X5))
% 0.19/0.46          | (r2_hidden @ X9 @ X7)
% 0.19/0.46          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X5))
% 0.19/0.46          | ((X9) != (k1_funct_1 @ X5 @ X10))
% 0.19/0.46          | ~ (v1_funct_1 @ X5)
% 0.19/0.46          | ~ (v1_relat_1 @ X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X5 : $i, X10 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X5)
% 0.19/0.46          | ~ (v1_funct_1 @ X5)
% 0.19/0.46          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X5))
% 0.19/0.46          | (r2_hidden @ (k1_funct_1 @ X5 @ X10) @ (k2_relat_1 @ X5)))),
% 0.19/0.46      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((r1_tarski @ sk_A @ X0)
% 0.19/0.46          | (r2_hidden @ (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_A))) @ 
% 0.19/0.46             (k2_relat_1 @ sk_B))
% 0.19/0.46          | ~ (v1_funct_1 @ sk_B)
% 0.19/0.46          | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['6', '8'])).
% 0.19/0.46  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((r1_tarski @ sk_A @ X0)
% 0.19/0.46          | (r2_hidden @ (k1_funct_1 @ sk_B @ (sk_D_2 @ (sk_C @ X0 @ sk_A))) @ 
% 0.19/0.46             (k2_relat_1 @ sk_B)))),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.19/0.46          | (r1_tarski @ sk_A @ X0)
% 0.19/0.46          | (r1_tarski @ sk_A @ X0))),
% 0.19/0.46      inference('sup+', [status(thm)], ['3', '12'])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((r1_tarski @ sk_A @ X0)
% 0.19/0.46          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.19/0.46      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (![X1 : $i, X3 : $i]:
% 0.19/0.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      (((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))
% 0.19/0.46        | (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.46  thf('17', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.19/0.46      inference('simplify', [status(thm)], ['16'])).
% 0.19/0.46  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
