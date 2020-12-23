%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y02Z7Wo440

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  55 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  415 ( 590 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t179_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( ( r1_tarski @ B @ C )
             => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t179_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ sk_A ) ) ),
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

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X8: $i,X9: $i] :
      ( ( X8
       != ( k10_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( sk_E_1 @ X9 @ X5 @ X6 ) @ X5 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k10_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( sk_E_1 @ X9 @ X5 @ X6 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X5: $i,X6: $i,X8: $i,X9: $i] :
      ( ( X8
       != ( k10_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X9 @ ( sk_E_1 @ X9 @ X5 @ X6 ) ) @ X6 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k10_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X9 @ ( sk_E_1 @ X9 @ X5 @ X6 ) ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_E_1 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( sk_E_1 @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ X0 @ sk_B ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( sk_E_1 @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ X0 @ sk_B ) ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X8: $i,X10: $i,X11: $i] :
      ( ( X8
       != ( k10_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X6 )
      | ~ ( r2_hidden @ X11 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r2_hidden @ X11 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X6 )
      | ( r2_hidden @ X10 @ ( k10_relat_1 @ X6 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( k10_relat_1 @ sk_C_1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ X0 @ sk_B ) @ X2 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( k10_relat_1 @ sk_C_1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ X0 @ sk_B ) @ X2 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k10_relat_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y02Z7Wo440
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 44 iterations in 0.069s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(t179_relat_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( v1_relat_1 @ C ) =>
% 0.20/0.52           ( ( r1_tarski @ B @ C ) =>
% 0.20/0.52             ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( v1_relat_1 @ B ) =>
% 0.20/0.52          ( ![C:$i]:
% 0.20/0.52            ( ( v1_relat_1 @ C ) =>
% 0.20/0.52              ( ( r1_tarski @ B @ C ) =>
% 0.20/0.52                ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t179_relat_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ sk_A) @ 
% 0.20/0.52          (k10_relat_1 @ sk_C_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d3_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf(d14_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i,C:$i]:
% 0.20/0.52         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.20/0.52           ( ![D:$i]:
% 0.20/0.52             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52               ( ?[E:$i]:
% 0.20/0.52                 ( ( r2_hidden @ E @ B ) & 
% 0.20/0.52                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.52         (((X8) != (k10_relat_1 @ X6 @ X5))
% 0.20/0.52          | (r2_hidden @ (sk_E_1 @ X9 @ X5 @ X6) @ X5)
% 0.20/0.52          | ~ (r2_hidden @ X9 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X6)
% 0.20/0.52          | ~ (r2_hidden @ X9 @ (k10_relat_1 @ X6 @ X5))
% 0.20/0.52          | (r2_hidden @ (sk_E_1 @ X9 @ X5 @ X6) @ X5))),
% 0.20/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (sk_E_1 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ X0 @ X1) @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.52         (((X8) != (k10_relat_1 @ X6 @ X5))
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ X9 @ (sk_E_1 @ X9 @ X5 @ X6)) @ X6)
% 0.20/0.52          | ~ (r2_hidden @ X9 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X6)
% 0.20/0.52          | ~ (r2_hidden @ X9 @ (k10_relat_1 @ X6 @ X5))
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ X9 @ (sk_E_1 @ X9 @ X5 @ X6)) @ X6))),
% 0.20/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.20/0.52              (sk_E_1 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.20/0.52             X1)
% 0.20/0.52          | ~ (v1_relat_1 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.52  thf('9', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | (r2_hidden @ X0 @ X2)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ sk_B)
% 0.20/0.52          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_C @ X1 @ (k10_relat_1 @ sk_B @ X0)) @ 
% 0.20/0.52              (sk_E_1 @ (sk_C @ X1 @ (k10_relat_1 @ sk_B @ X0)) @ X0 @ sk_B)) @ 
% 0.20/0.52             sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.52  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_C @ X1 @ (k10_relat_1 @ sk_B @ X0)) @ 
% 0.20/0.52              (sk_E_1 @ (sk_C @ X1 @ (k10_relat_1 @ sk_B @ X0)) @ X0 @ sk_B)) @ 
% 0.20/0.52             sk_C_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X8 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (((X8) != (k10_relat_1 @ X6 @ X5))
% 0.20/0.52          | (r2_hidden @ X10 @ X8)
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X6)
% 0.20/0.52          | ~ (r2_hidden @ X11 @ X5)
% 0.20/0.52          | ~ (v1_relat_1 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X6)
% 0.20/0.52          | ~ (r2_hidden @ X11 @ X5)
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X6)
% 0.20/0.52          | (r2_hidden @ X10 @ (k10_relat_1 @ X6 @ X5)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X1 @ (k10_relat_1 @ sk_B @ X0)) @ 
% 0.20/0.52             (k10_relat_1 @ sk_C_1 @ X2))
% 0.20/0.52          | ~ (r2_hidden @ 
% 0.20/0.52               (sk_E_1 @ (sk_C @ X1 @ (k10_relat_1 @ sk_B @ X0)) @ X0 @ sk_B) @ 
% 0.20/0.52               X2)
% 0.20/0.52          | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.52  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X1 @ (k10_relat_1 @ sk_B @ X0)) @ 
% 0.20/0.52             (k10_relat_1 @ sk_C_1 @ X2))
% 0.20/0.52          | ~ (r2_hidden @ 
% 0.20/0.52               (sk_E_1 @ (sk_C @ X1 @ (k10_relat_1 @ sk_B @ X0)) @ X0 @ sk_B) @ 
% 0.20/0.52               X2))),
% 0.20/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ sk_B)
% 0.20/0.52          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X1 @ (k10_relat_1 @ sk_B @ X0)) @ 
% 0.20/0.52             (k10_relat_1 @ sk_C_1 @ X0))
% 0.20/0.52          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '19'])).
% 0.20/0.52  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X1 @ (k10_relat_1 @ sk_B @ X0)) @ 
% 0.20/0.52             (k10_relat_1 @ sk_C_1 @ X0))
% 0.20/0.52          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1))),
% 0.20/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_C @ X1 @ (k10_relat_1 @ sk_B @ X0)) @ 
% 0.20/0.52           (k10_relat_1 @ sk_C_1 @ X0))
% 0.20/0.52          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ X1))),
% 0.20/0.52      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k10_relat_1 @ sk_C_1 @ X0))
% 0.20/0.52          | (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ 
% 0.20/0.52             (k10_relat_1 @ sk_C_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k10_relat_1 @ sk_C_1 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.52  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
