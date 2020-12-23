%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nDbzAX1nOO

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:06 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  399 ( 464 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

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

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D_1 @ X8 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X13
       != ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) ) @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('6',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( sk_F_1 @ ( sk_D_1 @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( sk_F_1 @ ( sk_D_1 @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( sk_F_1 @ ( sk_D_1 @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t44_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_relat_1])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['17','18','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nDbzAX1nOO
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 123 iterations in 0.125s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.58  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.39/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.39/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.58  thf(dt_k5_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.39/0.58       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (![X19 : $i, X20 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X19)
% 0.39/0.58          | ~ (v1_relat_1 @ X20)
% 0.39/0.58          | (v1_relat_1 @ (k5_relat_1 @ X19 @ X20)))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.39/0.58  thf(d3_tarski, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X1 : $i, X3 : $i]:
% 0.39/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf(d4_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.39/0.58       ( ![C:$i]:
% 0.39/0.58         ( ( r2_hidden @ C @ B ) <=>
% 0.39/0.58           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X8 @ X7)
% 0.39/0.58          | (r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 0.39/0.58          | ((X7) != (k1_relat_1 @ X6)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X6 : $i, X8 : $i]:
% 0.39/0.58         ((r2_hidden @ (k4_tarski @ X8 @ (sk_D_1 @ X8 @ X6)) @ X6)
% 0.39/0.58          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X6)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.39/0.58          | (r2_hidden @ 
% 0.39/0.58             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.39/0.58              (sk_D_1 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 0.39/0.58             X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '3'])).
% 0.39/0.58  thf(d8_relat_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( v1_relat_1 @ B ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( v1_relat_1 @ C ) =>
% 0.39/0.58               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.39/0.58                 ( ![D:$i,E:$i]:
% 0.39/0.58                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.39/0.58                     ( ?[F:$i]:
% 0.39/0.58                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.39/0.58                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X17 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X11)
% 0.39/0.58          | ((X13) != (k5_relat_1 @ X12 @ X11))
% 0.39/0.58          | (r2_hidden @ 
% 0.39/0.58             (k4_tarski @ X14 @ (sk_F_1 @ X17 @ X14 @ X11 @ X12)) @ X12)
% 0.39/0.58          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ X13)
% 0.39/0.58          | ~ (v1_relat_1 @ X13)
% 0.39/0.58          | ~ (v1_relat_1 @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i, X14 : $i, X17 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X12)
% 0.39/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 0.39/0.58          | ~ (r2_hidden @ (k4_tarski @ X14 @ X17) @ (k5_relat_1 @ X12 @ X11))
% 0.39/0.58          | (r2_hidden @ 
% 0.39/0.58             (k4_tarski @ X14 @ (sk_F_1 @ X17 @ X14 @ X11 @ X12)) @ X12)
% 0.39/0.58          | ~ (v1_relat_1 @ X11))),
% 0.39/0.58      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ X2)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | (r2_hidden @ 
% 0.39/0.58             (k4_tarski @ 
% 0.39/0.58              (sk_C @ X2 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.39/0.58              (sk_F_1 @ 
% 0.39/0.58               (sk_D_1 @ (sk_C @ X2 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.39/0.58                (k5_relat_1 @ X1 @ X0)) @ 
% 0.39/0.58               (sk_C @ X2 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0 @ X1)) @ 
% 0.39/0.58             X1)
% 0.39/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ X1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X1)
% 0.39/0.58          | (r2_hidden @ 
% 0.39/0.58             (k4_tarski @ 
% 0.39/0.58              (sk_C @ X2 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.39/0.58              (sk_F_1 @ 
% 0.39/0.58               (sk_D_1 @ (sk_C @ X2 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.39/0.58                (k5_relat_1 @ X1 @ X0)) @ 
% 0.39/0.58               (sk_C @ X2 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0 @ X1)) @ 
% 0.39/0.58             X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ X2))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '7'])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)) @ X2)
% 0.39/0.58          | (r2_hidden @ 
% 0.39/0.58             (k4_tarski @ 
% 0.39/0.58              (sk_C @ X2 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.39/0.58              (sk_F_1 @ 
% 0.39/0.58               (sk_D_1 @ (sk_C @ X2 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 0.39/0.58                (k5_relat_1 @ X1 @ X0)) @ 
% 0.39/0.58               (sk_C @ X2 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ X0 @ X1)) @ 
% 0.39/0.58             X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['8'])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.58         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.39/0.58          | (r2_hidden @ X4 @ X7)
% 0.39/0.58          | ((X7) != (k1_relat_1 @ X6)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.58         ((r2_hidden @ X4 @ (k1_relat_1 @ X6))
% 0.39/0.58          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 0.39/0.58      inference('simplify', [status(thm)], ['10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)) @ X2)
% 0.39/0.58          | (r2_hidden @ (sk_C @ X2 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))) @ 
% 0.39/0.58             (k1_relat_1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['9', '11'])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X1 : $i, X3 : $i]:
% 0.39/0.58         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)) @ 
% 0.39/0.58           (k1_relat_1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X1)
% 0.39/0.58          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)) @ 
% 0.39/0.58             (k1_relat_1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)) @ 
% 0.39/0.58             (k1_relat_1 @ X0)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['14'])).
% 0.39/0.58  thf(t44_relat_1, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( v1_relat_1 @ B ) =>
% 0.39/0.58           ( r1_tarski @
% 0.39/0.58             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( v1_relat_1 @ A ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( v1_relat_1 @ B ) =>
% 0.39/0.58              ( r1_tarski @
% 0.39/0.58                ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t44_relat_1])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) @ 
% 0.39/0.58          (k1_relat_1 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('17', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.58  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('20', plain, ($false),
% 0.39/0.58      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
