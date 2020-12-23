%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ccDpvhAUCM

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:01 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :   15
%              Number of atoms          :  418 ( 495 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

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

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k4_tarski @ ( sk_C_1 @ X10 ) @ ( sk_D_1 @ X10 ) ) )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C @ X1 @ X0 )
        = ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k7_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ D @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( X4
       != ( k7_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k7_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ X5 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k7_relat_1 @ X3 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ X0 ) ) ) @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( sk_D_1 @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( sk_D_1 @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( sk_D_1 @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( sk_D_1 @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t88_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t88_relat_1])).

thf('21',plain,(
    ~ ( r1_tarski @ ( k7_relat_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ccDpvhAUCM
% 0.16/0.37  % Computer   : n006.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 20:47:22 EST 2020
% 0.23/0.37  % CPUTime    : 
% 0.23/0.37  % Running portfolio for 600 s
% 0.23/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.37  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 100 iterations in 0.151s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.63  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.63  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.45/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.63  thf(dt_k7_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      (![X15 : $i, X16 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k7_relat_1 @ X15 @ X16)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.45/0.63  thf(d3_tarski, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (![X1 : $i, X3 : $i]:
% 0.45/0.63         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.63  thf(d1_relat_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ A ) <=>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ~( ( r2_hidden @ B @ A ) & 
% 0.45/0.63              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i]:
% 0.45/0.63         (((X10) = (k4_tarski @ (sk_C_1 @ X10) @ (sk_D_1 @ X10)))
% 0.45/0.63          | ~ (r2_hidden @ X10 @ X11)
% 0.45/0.63          | ~ (v1_relat_1 @ X11))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((r1_tarski @ X0 @ X1)
% 0.45/0.63          | ~ (v1_relat_1 @ X0)
% 0.45/0.63          | ((sk_C @ X1 @ X0)
% 0.45/0.63              = (k4_tarski @ (sk_C_1 @ (sk_C @ X1 @ X0)) @ 
% 0.45/0.63                 (sk_D_1 @ (sk_C @ X1 @ X0)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (![X15 : $i, X16 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k7_relat_1 @ X15 @ X16)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X1 : $i, X3 : $i]:
% 0.45/0.63         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((r1_tarski @ X0 @ X1)
% 0.45/0.63          | ~ (v1_relat_1 @ X0)
% 0.45/0.63          | ((sk_C @ X1 @ X0)
% 0.45/0.63              = (k4_tarski @ (sk_C_1 @ (sk_C @ X1 @ X0)) @ 
% 0.45/0.63                 (sk_D_1 @ (sk_C @ X1 @ X0)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.63  thf(d11_relat_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ A ) =>
% 0.45/0.63       ( ![B:$i,C:$i]:
% 0.45/0.63         ( ( v1_relat_1 @ C ) =>
% 0.45/0.63           ( ( ( C ) = ( k7_relat_1 @ A @ B ) ) <=>
% 0.45/0.63             ( ![D:$i,E:$i]:
% 0.45/0.63               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.45/0.63                 ( ( r2_hidden @ D @ B ) & 
% 0.45/0.63                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X4)
% 0.45/0.63          | ((X4) != (k7_relat_1 @ X5 @ X6))
% 0.45/0.63          | (r2_hidden @ (k4_tarski @ X7 @ X9) @ X5)
% 0.45/0.63          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ X4)
% 0.45/0.63          | ~ (v1_relat_1 @ X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [d11_relat_1])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X5)
% 0.45/0.63          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k7_relat_1 @ X5 @ X6))
% 0.45/0.63          | (r2_hidden @ (k4_tarski @ X7 @ X9) @ X5)
% 0.45/0.63          | ~ (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['7'])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ (k7_relat_1 @ X3 @ X2))
% 0.45/0.63          | ~ (v1_relat_1 @ X0)
% 0.45/0.63          | (r1_tarski @ X0 @ X1)
% 0.45/0.63          | ~ (v1_relat_1 @ (k7_relat_1 @ X3 @ X2))
% 0.45/0.63          | (r2_hidden @ 
% 0.45/0.63             (k4_tarski @ (sk_C_1 @ (sk_C @ X1 @ X0)) @ 
% 0.45/0.63              (sk_D_1 @ (sk_C @ X1 @ X0))) @ 
% 0.45/0.63             X3)
% 0.45/0.63          | ~ (v1_relat_1 @ X3))),
% 0.45/0.63      inference('sup-', [status(thm)], ['6', '8'])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.45/0.63          | ~ (v1_relat_1 @ X1)
% 0.45/0.63          | (r2_hidden @ 
% 0.45/0.63             (k4_tarski @ (sk_C_1 @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0))) @ 
% 0.45/0.63              (sk_D_1 @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0)))) @ 
% 0.45/0.63             X1)
% 0.45/0.63          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.45/0.63          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.45/0.63          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['5', '9'])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.45/0.63          | (r2_hidden @ 
% 0.45/0.63             (k4_tarski @ (sk_C_1 @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0))) @ 
% 0.45/0.63              (sk_D_1 @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0)))) @ 
% 0.45/0.63             X1)
% 0.45/0.63          | ~ (v1_relat_1 @ X1)
% 0.45/0.63          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2))),
% 0.45/0.63      inference('simplify', [status(thm)], ['10'])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X1)
% 0.45/0.63          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.45/0.63          | ~ (v1_relat_1 @ X1)
% 0.45/0.63          | (r2_hidden @ 
% 0.45/0.63             (k4_tarski @ (sk_C_1 @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0))) @ 
% 0.45/0.63              (sk_D_1 @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0)))) @ 
% 0.45/0.63             X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['4', '11'])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((r2_hidden @ 
% 0.45/0.63           (k4_tarski @ (sk_C_1 @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0))) @ 
% 0.45/0.63            (sk_D_1 @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0)))) @ 
% 0.45/0.63           X1)
% 0.45/0.63          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.45/0.63          | ~ (v1_relat_1 @ X1))),
% 0.45/0.63      inference('simplify', [status(thm)], ['12'])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((r2_hidden @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0)) @ X1)
% 0.45/0.63          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.45/0.63          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.45/0.63          | ~ (v1_relat_1 @ X1)
% 0.45/0.63          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2))),
% 0.45/0.63      inference('sup+', [status(thm)], ['3', '13'])).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X1)
% 0.45/0.63          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.45/0.63          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.45/0.63          | (r2_hidden @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0)) @ X1))),
% 0.45/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X1)
% 0.45/0.63          | (r2_hidden @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0)) @ X1)
% 0.45/0.63          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.45/0.63          | ~ (v1_relat_1 @ X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['0', '15'])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.45/0.63          | (r2_hidden @ (sk_C @ X2 @ (k7_relat_1 @ X1 @ X0)) @ X1)
% 0.45/0.63          | ~ (v1_relat_1 @ X1))),
% 0.45/0.63      inference('simplify', [status(thm)], ['16'])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      (![X1 : $i, X3 : $i]:
% 0.45/0.63         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X0)
% 0.45/0.63          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X0)
% 0.45/0.63          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X0) | ~ (v1_relat_1 @ X0))),
% 0.45/0.63      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.63  thf(t88_relat_1, conjecture,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i]:
% 0.45/0.63        ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t88_relat_1])).
% 0.45/0.63  thf('21', plain, (~ (r1_tarski @ (k7_relat_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('22', plain, (~ (v1_relat_1 @ sk_B_1)),
% 0.45/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.63  thf('23', plain, ((v1_relat_1 @ sk_B_1)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('24', plain, ($false), inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
