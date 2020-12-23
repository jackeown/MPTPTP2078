%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NAVKWUQEFW

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :  272 ( 307 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X7 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(d12_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k8_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ E @ A )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X6 @ X7 ) @ ( sk_D_1 @ X6 @ X7 ) ) @ X6 )
      | ( r1_tarski @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t117_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t117_relat_1])).

thf('13',plain,(
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NAVKWUQEFW
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 85 iterations in 0.066s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.51  thf(dt_k8_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.20/0.51  thf(d3_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.52           ( ![C:$i,D:$i]:
% 0.20/0.52             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.20/0.52               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         ((r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ X7)
% 0.20/0.52          | (r1_tarski @ X7 @ X6)
% 0.20/0.52          | ~ (v1_relat_1 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.20/0.52  thf(d12_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( v1_relat_1 @ C ) =>
% 0.20/0.52           ( ( ( C ) = ( k8_relat_1 @ A @ B ) ) <=>
% 0.20/0.52             ( ![D:$i,E:$i]:
% 0.20/0.52               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.20/0.52                 ( ( r2_hidden @ E @ A ) & 
% 0.20/0.52                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0)
% 0.20/0.52          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X2)
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 0.20/0.52          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.52          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.52          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.20/0.52              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 0.20/0.52             X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.20/0.52              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 0.20/0.52             X0)
% 0.20/0.52          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.52          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0)
% 0.20/0.52          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.20/0.52              (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 0.20/0.52             X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r2_hidden @ 
% 0.20/0.52           (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.20/0.52            (sk_D_1 @ X2 @ (k8_relat_1 @ X1 @ X0))) @ 
% 0.20/0.52           X0)
% 0.20/0.52          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.52          | ~ (v1_relat_1 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X6 @ X7) @ (sk_D_1 @ X6 @ X7)) @ 
% 0.20/0.52             X6)
% 0.20/0.52          | (r1_tarski @ X7 @ X6)
% 0.20/0.52          | ~ (v1_relat_1 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0)
% 0.20/0.52          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.52          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.52          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i]:
% 0.20/0.52         ((v1_relat_1 @ (k8_relat_1 @ X11 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X0) | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0))),
% 0.20/0.52      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf(t117_relat_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t117_relat_1])).
% 0.20/0.52  thf('13', plain, (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain, (~ (v1_relat_1 @ sk_B)),
% 0.20/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('16', plain, ($false), inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.36/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
